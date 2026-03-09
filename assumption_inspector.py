import math
import pm4py
from pm4py.ocel import ocel_get_object_types, ocel_object_type_activities
from pm4py import ocel_objects_interactions_summary, ocel_objects_summary
import sys
import numpy
from functools import reduce
import itertools

BAR = "================================================================================"

def import_ocel(filename):
  #print("Import started")
  if "xml" in filename:
    ocel = pm4py.read_ocel2_xml(filename)
  elif "json" in filename:
    ocel = pm4py.read_ocel2_json(filename)
  else:
    raise Exception("Unexpected file format, expected .xml or .json")
  #print("Import done")
  sys.stdout.flush()
  return ocel

def get_object_type_dict(ocel, object_types):
  types_of_objects = {}
  myobjects  = ocel.objects.reset_index() 
  for index, row in myobjects.iterrows():
    types_of_objects[row["ocel:oid"]] = row["ocel:type"]
  return types_of_objects

def static_object_relationships(object_summary, types_of_objects, object_types):
  distinct_object_types = [tuple([t1,t2]) \
    for t1 in object_types for t2 in object_types if t1 != t2]
  relationships = dict([ (ts, []) for ts in distinct_object_types ])
  # walk over objects
  partners = {}
  object_summary  = object_summary.reset_index() 
  for _, row in object_summary.iterrows():
    oid = row["ocel:oid"]
    otype = types_of_objects[oid]
    partners[oid] = row["interacting_objects"]
    interacting_types = [ types_of_objects[pid] for pid in partners[oid]]
    for mtype in object_types:
      mobjects = [ x for x in partners[oid] if types_of_objects[x] == mtype]
      num_m_partners = len(mobjects)
      if otype != mtype:
        key = tuple([otype,mtype])
        relationships[key].append(num_m_partners)
  return relationships


def dynamic_object_relationships(object_summary, types_of_objects, object_types):
  distinct_object_types = [tuple([t1,t2]) \
    for t1 in object_types for t2 in object_types if t1 != t2]
  relationships = dict([ (ts, []) for ts in distinct_object_types ])

  for _, r in ocel.get_extended_table().iterrows():
    rd = r.to_dict()
    for mtype in object_types:
      ms = rd["ocel:type:"+mtype] 
      if isinstance(ms, list) and len(ms) > 0:
        num_m_partners = len(ms)
        for otype in object_types:
          os = rd["ocel:type:"+otype]
          if isinstance(os, list) and len(os) > 0 and otype != mtype:
            key = tuple([otype,mtype])
            relationships[key].append(num_m_partners)
  return relationships

def classify_relationships(relationships, silent = False):
  to_one = []
  to_almost_one = []
  to_many = []
  to_many_dyn = []

  if not silent:
    print("INTERACTION COUNTS")
  for ((otype,mtype), counts) in relationships.items():
    if len(counts) > 0:
      ratio = float(sum(counts)) / len(counts)
      cmax = max(counts)
      cmin = min(counts)
      if cmax == 0:
        continue # no interactions at all, so we ignore this relationship
      if not silent:
        print("A %s interacts with [%d, %d] %s (on average %.3f)." % (otype, cmin, cmax, mtype, ratio))
      if ratio == 1.0:
        to_one.append(tuple([otype,mtype]))
      elif ratio > 1.0 and ratio <= 1.05:
        to_almost_one.append(tuple([otype,mtype]))
      else:
        to_many.append(tuple([otype,mtype]))
  print("")
  return to_one, to_almost_one, to_many

def classify_relationship_pairs(to_one, to_almost_one, to_many, static = True):
  distinct_object_types = [tuple([t1,t2]) \
    for t1 in object_types for t2 in object_types if t1 != t2]
  rel_kinds = {"one2one": [], "one2almostone": [],"almostone2almostone": [],"many2one": [], "many2almostone": [], "many2many": []}
  for type_pair in distinct_object_types:
    (type1, type2) = type_pair
    if type1 < type2:
      continue # just to process every pair only once
    rtype_pair = tuple([type2, type1])
    if type_pair in to_one and rtype_pair in to_one:
      rel_kinds["one2one"].append(type_pair)
    elif type_pair in to_one and rtype_pair in to_almost_one:
      rel_kinds["one2almostone"].append(rtype_pair)
    elif rtype_pair in to_one and type_pair in to_almost_one:
      rel_kinds["one2almostone"].append(type_pair)
    elif rtype_pair in to_almost_one and type_pair in to_almost_one:
      rel_kinds["almostone2almostone"].append(type_pair)
    elif type_pair in to_one and rtype_pair in to_many:
      rel_kinds["many2one"].append(type_pair)
    elif rtype_pair in to_one and type_pair in to_many:
      rel_kinds["many2one"].append(rtype_pair)
    elif type_pair in to_almost_one and rtype_pair in to_many:
      rel_kinds["many2almostone"].append(type_pair)
    elif rtype_pair in to_almost_one and type_pair in to_many:
      rel_kinds["many2almostone"].append(rtype_pair)
    elif type_pair in to_many and rtype_pair in to_many:
      rel_kinds["many2many"].append(type_pair)

  print("%s RELATIONSHIP TYPES" % ("STATIC" if static else "DYNAMIC"))
  for (kind, type_pairs) in rel_kinds.items():
    if len(type_pairs) == 0:
      continue
    ls = reduce(lambda acc, ts: "(%s, %s), %s" % (ts[0], ts[1], acc), type_pairs, "")
    print("%d %s: %s" % (len(type_pairs), kind, ls))
  print("")
  am2o = [(mt, ot) for (ot, mt) in rel_kinds["one2almostone"] ]
  return rel_kinds["one2one"], am2o + rel_kinds["many2one"]


def get_object_summary(ocel):
  object_summary = ocel_objects_summary(ocel)
  for col in ['activities_lifecycle', 'lifecycle_start', 'lifecycle_end', 'lifecycle_duration']:
    object_summary = object_summary.drop(col, axis=1)
  return object_summary


def find_reference_types(ocel, object_types):
  objtype_count_for_events = {}
  for _, r in ocel.get_extended_table().iterrows():
    rd = r.to_dict()
    event_type = rd["ocel:activity"]
    if not event_type in objtype_count_for_events:
      objtype_count_for_events[event_type] = dict([ (t,[]) for t in object_types])

    for t in object_types:
      if isinstance(rd["ocel:type:"+t], list):
        cnt = len(rd["ocel:type:"+t])
        objtype_count_for_events[event_type][t].append(cnt)
      else:
        objtype_count_for_events[event_type][t].append(0)

  reftypes = {}
  refcombos = 1
  for (e, objts) in objtype_count_for_events.items():
    reftypes[e] = [ t for t in objts.keys() if min(objts[t]) == 1 and  max(objts[t]) == 1]
    if len(reftypes[e]) > 1:
      reftypes[e].remove("Session")  # AoE
    if len(reftypes[e]) > 1:
      reftypes[e].remove("Match") # AoE
    print(" %s %d reftype candidates" % (e, len(reftypes[e])), reftypes[e])
    # refcombos = refcombos * len(reftypes[e])
    for t in objts.keys():
      if max(objts[t]) == 0:
        continue
      print("   %s: min %d max %d avg %.2f" % (t, min(objts[t]), max(objts[t]), sum(objts[t])/ len(objts[t])))

  print("combos", refcombos)
  return reftypes

def get_objects_from_event_row(rd, object_types):
  objects = {}
  for t in object_types:
    objs = rd["ocel:type:"+t]
    if not isinstance(objs, list):
      continue 
    objects[t] = objs
  return objects


def events_only_modify_properties_of_refobjects_aux(ocel, object_types, m2o, reftypes, minv):
  parents = {} # map (many-type object, one-type) to (one-type object)
  violated = 0
  events = 0
  ts = None
  for _, r in ocel.get_extended_table().iterrows():
    event_ok = True
    rd = r.to_dict()
    event_type = rd["ocel:activity"]

    # assert that events are ordered by timestamp
    timestamp = rd["ocel:timestamp"]
    assert(ts == None or timestamp >= ts)
    ts = timestamp

    objs = get_objects_from_event_row(rd, object_types)

    # update FIRST links for reference object
    reftype = reftypes[event_type]
    refobjs = objs[reftype]
    assert(len(refobjs) == 1)
    refobj = refobjs[0]
    to_parent_links = [ (t2, objs2) for (mt,ot) in m2o \
                         for (t2, objs2) in objs.items() if mt == reftype and ot == t2]
    to_children_links = [ (t2, o) for (mt, ot) in m2o \
                           for (t2, objs2) in objs.items() \
                            for o in objs2 if ot == reftype and mt == t2]

    for (t2, objs2) in to_parent_links: # Assumption 4a
      assert(len(objs2) == 1) # because this is a parent object
      # print("Fix link for %s of type %s to %s" % (refobj, t2, objs2[0]), timestamp)
      parents[(refobj, t2)] = objs2[0]

    for (t2, o2) in to_children_links: # Assumption 4b
      # print("Fix link for %s of type %s to %s" % (o2, t1, refobj), timestamp)
      parents[(o2, reftype)] = refobj
    
    for (t1, objs1) in objs.items():
      to_parent_links = [ (t2, objs2) for (mt,ot) in m2o \
                         for (t2, objs2) in objs.items() if mt == t1 and ot == t2]
      to_children_links = [ (t2, o) for (mt, ot) in m2o \
                           for (t2, objs2) in objs.items() \
                            for o in objs2 if ot == t1 and mt == t2]
      if t1 != reftypes[event_type]: # not reference type
        # check other relationships mentioned
        for (t2, objs2) in to_parent_links: # Assumption 4a
          assert(len(objs2) == 1) # because this is a parent object
          for o1 in objs1:
            if (o1, t2) not in parents or not parents[(o1, t2)] == objs2[0]:
              # print("Violation: link for %s of type %s is not %s" % (o1, t2, objs2[0]), timestamp)
              event_ok = False

        for (t2, o2) in to_children_links: # Assumption 4b
          assert(len(objs1) == 1) # because this is a parent object
          if (o2, t1) not in parents or not parents[(o2, t1)] == objs1[0]:
            # print("Violation: link for %s of type %s is not %s" % (o2, t1, objs1[0]), timestamp)
            event_ok = False
    events += 1
    if events % 1000 == 0:
      print("%d events processed, %d violations so far (%.2f perc ok)" % (events, violated, 1.0 - violated/events))
      sys.stdout.flush()
    if not event_ok:
      violated += 1
      if violated >= minv:
        return minv

  cnt = len(ocel.get_extended_table())
  p = 1.0 - violated/cnt
  print("%d of %d violations (%.2f perc ok)" % (violated, cnt, p))
  sys.stdout.flush()
  return violated

      
def events_only_modify_properties_of_refobjects(ocel, object_types, m2o, reftype_candidates):
  # print(reftype_candidates)
  cands = [ [(e, t) for t in ts] for (e, ts) in reftype_candidates.items()]
  reftypes = itertools.product(*cands)
  minv = 100000
  minref = None
  #combos = list(reftypes)
  #print("%d possible reference type combos" % len(combos))
  for combo in reftypes:
    v = events_only_modify_properties_of_refobjects_aux(ocel, object_types, m2o, dict(combo), minv)
    if v < minv:
      minv = v
      minref = combo
    if v == 0:
      break
  print("FINALLY: minimal number of violations is %d using reftypes" % minv, minref)


          



if __name__ == "__main__":
  ocel = import_ocel(sys.argv[1])

  print(BAR, "\n", sys.argv[1])
  print(BAR)
  object_types = ocel_get_object_types(ocel)
  print("OBJECT TYPES")
  print(object_types, "\n")


  # determine object types
  types_of_objects = get_object_type_dict(ocel, object_types)

  # determine static relationships
  object_summary = get_object_summary(ocel)
  relationships = static_object_relationships(object_summary, types_of_objects, object_types)
  to_one, to_almost_one, to_many = classify_relationships(relationships, silent = False)
  classify_relationship_pairs(to_one, to_almost_one, to_many)
  
  # determine dynamic relationships
  relationships = dynamic_object_relationships(ocel, types_of_objects, object_types)
  to_one, to_almost_one, to_many = classify_relationships(relationships, silent = False)
  o2o, m2o = classify_relationship_pairs(to_one, to_almost_one, to_many, static = False)

  # check Assumption 3
  reftype_candidates = find_reference_types(ocel, object_types)

  # check Assumption 5
  events_only_modify_properties_of_refobjects(ocel, object_types, m2o, reftype_candidates)
