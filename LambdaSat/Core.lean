/-
  LambdaSat — Generic E-Graph Core
  Domain-agnostic e-graph parameterized by operation type Op.
  Generalized from VR1CS-Lean v1.3.0 (replaces CircuitNodeOp with typeclass).
-/
import Lean
import LambdaSat.UnionFind

namespace LambdaSat

/-- Typeclass for e-graph node operations.
    Any domain-specific node type must implement this interface. -/
class NodeOps (Op : Type) where
  /-- Extract child e-class IDs from an operation. -/
  children : Op → List EClassId
  /-- Apply a function to all child e-class IDs. -/
  mapChildren : (EClassId → EClassId) → Op → Op
  /-- Replace children positionally with new IDs.
      `replaceChildren op [c0, c1, ...]` creates a new op with children replaced. -/
  replaceChildren : Op → List EClassId → Op
  /-- Law: `mapChildren f` transforms the children list by `List.map f`. -/
  mapChildren_children : ∀ (f : EClassId → EClassId) (op : Op),
    children (mapChildren f op) = (children op).map f

/-- An e-node wraps a domain-specific operation. -/
structure ENode (Op : Type) where
  op : Op

-- Manual BEq/Hashable instances (Lean 4.26 cannot auto-derive for parameterized types)
instance {Op : Type} [BEq Op] : BEq (ENode Op) where
  beq a b := a.op == b.op

instance {Op : Type} [Hashable Op] : Hashable (ENode Op) where
  hash a := hash a.op

instance {Op : Type} [BEq Op] [LawfulBEq Op] : LawfulBEq (ENode Op) where
  eq_of_beq {a b} h := by
    have : a.op = b.op := eq_of_beq h
    exact congrArg ENode.mk this
  rfl {a} := beq_self_eq_true a.op

instance {Op : Type} [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op] :
    LawfulHashable (ENode Op) where
  hash_eq {a b} h := by
    have : a.op = b.op := eq_of_beq h
    show hash a.op = hash b.op
    rw [this]

instance {Op : Type} [Inhabited Op] : Inhabited (ENode Op) where
  default := ⟨default⟩

namespace ENode

variable {Op : Type} [NodeOps Op]

def children (node : ENode Op) : List EClassId :=
  NodeOps.children node.op

def mapChildren (f : EClassId → EClassId) (node : ENode Op) : ENode Op :=
  ⟨NodeOps.mapChildren f node.op⟩

@[simp] theorem mapChildren_children (f : EClassId → EClassId) (node : ENode Op) :
    (node.mapChildren f).children = node.children.map f := by
  simp [children, mapChildren, NodeOps.mapChildren_children]

end ENode

private def infinityCost : Nat := 1000000000

/-- An equivalence class: array of equivalent e-nodes + best cost tracking. -/
structure EClass (Op : Type) where
  nodes    : Array (ENode Op) := #[]
  bestCost : Nat := infinityCost
  bestNode : Option (ENode Op) := none

instance {Op : Type} : Inhabited (EClass Op) where
  default := ⟨#[], infinityCost, none⟩

namespace EClass

variable {Op : Type} [BEq Op]

def singleton (node : ENode Op) : EClass Op where
  nodes := #[node]
  bestCost := infinityCost
  bestNode := some node

def addNode (ec : EClass Op) (node : ENode Op) : EClass Op :=
  if ec.nodes.contains node then ec
  else { ec with nodes := ec.nodes.push node }

def updateBest (ec : EClass Op) (node : ENode Op) (cost : Nat) : EClass Op :=
  if cost < ec.bestCost then
    { ec with bestCost := cost, bestNode := some node }
  else ec

def union (ec1 ec2 : EClass Op) : EClass Op :=
  let merged := ec2.nodes.foldl (fun acc n =>
    if acc.contains n then acc else acc.push n) ec1.nodes
  { nodes := merged
  , bestCost := min ec1.bestCost ec2.bestCost
  , bestNode := if ec1.bestCost ≤ ec2.bestCost then ec1.bestNode else ec2.bestNode }

def size (ec : EClass Op) : Nat := ec.nodes.size

end EClass

/-- The main E-graph, parameterized by operation type Op. -/
structure EGraph (Op : Type) [BEq Op] [Hashable Op] where
  unionFind : UnionFind := .empty
  hashcons  : Std.HashMap (ENode Op) EClassId := Std.HashMap.ofList []
  classes   : Std.HashMap EClassId (EClass Op) := Std.HashMap.ofList []
  worklist  : List EClassId := []
  dirtyArr  : Array EClassId := #[]

instance {Op : Type} [BEq Op] [Hashable Op] : Inhabited (EGraph Op) where
  default := ⟨.empty, Std.HashMap.ofList [], Std.HashMap.ofList [], [], #[]⟩

namespace EGraph

variable {Op : Type} [BEq Op] [Hashable Op]

def empty : EGraph Op :=
  ⟨.empty, Std.HashMap.ofList [], Std.HashMap.ofList [], [], #[]⟩

def numClasses (g : EGraph Op) : Nat := g.classes.size
def numNodes (g : EGraph Op) : Nat := g.hashcons.size

def find (g : EGraph Op) (id : EClassId) : (EClassId × EGraph Op) :=
  let (canonical, uf') := g.unionFind.find id
  (canonical, { g with unionFind := uf' })

variable [NodeOps Op] in
def canonicalize (g : EGraph Op) (node : ENode Op) : (ENode Op × EGraph Op) :=
  let children := node.children
  if children.isEmpty then (node, g)
  else
    let rec go (cs : List EClassId) (g : EGraph Op) (pairs : List (EClassId × EClassId)) :
        (List (EClassId × EClassId) × EGraph Op) :=
      match cs with
      | [] => (pairs, g)
      | c :: rest =>
        let (canonId, g') := g.find c
        go rest g' ((c, canonId) :: pairs)
    let (pairs, g') := go children g []
    let f : EClassId → EClassId := fun id =>
      match pairs.find? (fun (old, _) => old == id) with
      | some (_, new_) => new_
      | none => id
    (node.mapChildren f, g')

variable [NodeOps Op] in
def add (g : EGraph Op) (node : ENode Op) : (EClassId × EGraph Op) :=
  let (canonNode, g1) := g.canonicalize node
  match g1.hashcons.get? canonNode with
  | some existingId =>
    let (canonId, g2) := g1.find existingId
    (canonId, g2)
  | none =>
    let (newId, uf') := g1.unionFind.add
    let newClass := EClass.singleton canonNode
    (newId, { g1 with
      unionFind := uf'
      hashcons := g1.hashcons.insert canonNode newId
      classes := g1.classes.insert newId newClass })

def merge (g : EGraph Op) (id1 id2 : EClassId) : EGraph Op :=
  let (root1, g1) := g.find id1
  let (root2, g2) := g1.find id2
  if root1 == root2 then g2
  else
    let uf' := g2.unionFind.union root1 root2
    let class1 := g2.classes.get? root1 |>.getD default
    let class2 := g2.classes.get? root2 |>.getD default
    let mergedClass := class1.union class2
    { g2 with
      unionFind := uf'
      classes := g2.classes.insert root1 mergedClass
      worklist := root2 :: g2.worklist
      dirtyArr := if g2.dirtyArr.contains root1 then g2.dirtyArr
                  else g2.dirtyArr.push root1 }

variable [NodeOps Op] in
def processClass (g : EGraph Op) (classId : EClassId) :
    (EGraph Op × List (EClassId × EClassId)) :=
  let (canonId, g1) := g.find classId
  match g1.classes.get? canonId with
  | none => (g1, [])
  | some eclass =>
    eclass.nodes.foldl (init := (g1, [])) fun (acc, merges) node =>
      let (canonNode, acc1) := acc.canonicalize node
      if canonNode == node then
        (acc1, merges)
      else
        let hashcons1 := acc1.hashcons.erase node
        match hashcons1.get? canonNode with
        | some existingId =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, (canonId, existingId) :: merges)
        | none =>
          let hashcons2 := hashcons1.insert canonNode canonId
          ({ acc1 with hashcons := hashcons2 }, merges)

variable [NodeOps Op] in
partial def rebuild (g : EGraph Op) : EGraph Op :=
  if g.worklist.isEmpty && g.dirtyArr.isEmpty then g
  else
    let toProcess := g.worklist ++ g.dirtyArr.toList
    let g1 : EGraph Op := { g with worklist := [], dirtyArr := #[] }
    let (g2, pendingMerges) := toProcess.foldl (fun (acc, merges) classId =>
      let (acc', newMerges) := processClass acc classId
      (acc', newMerges ++ merges)
    ) (g1, [])
    let g3 := pendingMerges.foldl (fun acc (id1, id2) => acc.merge id1 id2) g2
    if g3.worklist.isEmpty && g3.dirtyArr.isEmpty then g3
    else rebuild g3

variable [NodeOps Op] in
partial def computeCosts (g : EGraph Op) (costFn : ENode Op → Nat) : EGraph Op :=
  let getCost (classes : Std.HashMap EClassId (EClass Op)) (id : EClassId) : Nat :=
    let (canonId, _) := g.unionFind.find id
    match classes.get? canonId with
    | some ec => ec.bestCost
    | none => infinityCost
  let iterate (classes : Std.HashMap EClassId (EClass Op)) :
      (Std.HashMap EClassId (EClass Op) × Bool) :=
    classes.fold (fun (acc, changed) classId eclass =>
      let (bestCost, bestNode, nodeChanged) := eclass.nodes.foldl
        (init := (eclass.bestCost, eclass.bestNode, false))
        fun (curBest, curNode, curChanged) node =>
          let childCosts := node.children.foldl
            (fun sum cid => sum + getCost acc cid) 0
          let cost := costFn node + childCosts
          if cost < curBest then (cost, some node, true)
          else (curBest, curNode, curChanged)
      if nodeChanged then
        let updatedClass := { eclass with bestCost := bestCost, bestNode := bestNode }
        (acc.insert classId updatedClass, true)
      else
        (acc, changed)) (classes, false)
  let rec loop (classes : Std.HashMap EClassId (EClass Op)) (fuel : Nat) :
      Std.HashMap EClassId (EClass Op) :=
    if fuel == 0 then classes
    else
      let (classes', changed) := iterate classes
      if changed then loop classes' (fuel - 1)
      else classes'
  { g with classes := loop g.classes 100 }

def getClass (g : EGraph Op) (id : EClassId) : (Option (EClass Op) × EGraph Op) :=
  let (canonId, g1) := g.find id
  (g1.classes.get? canonId, g1)

structure Stats where
  numClasses : Nat
  numNodes : Nat
  unionFindSize : Nat
  worklistSize : Nat
  deriving Repr

def stats (g : EGraph Op) : Stats where
  numClasses := g.numClasses
  numNodes := g.numNodes
  unionFindSize := g.unionFind.size
  worklistSize := g.worklist.length

end EGraph

end LambdaSat
