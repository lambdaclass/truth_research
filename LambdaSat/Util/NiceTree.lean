/-!
# LambdaSat.Util.NiceTree — Tree catamorphism with invariant preservation

Nice tree type and bottom-up fold (catamorphism) for DP on tree decompositions.
Adapted from VerifiedExtraction/Util/NiceTree.lean (0 sorry, 0 axioms).
-/

namespace LambdaSat.Util.NiceTree

inductive NiceTree (α : Type) where
  | leaf : α → NiceTree α
  | unary : α → NiceTree α → NiceTree α
  | binary : α → NiceTree α → NiceTree α → NiceTree α

def treeFold {α β : Type} (fL : α → β) (fU : α → β → β)
    (fB : α → β → β → β) : NiceTree α → β
  | .leaf a => fL a
  | .unary a t => fU a (treeFold fL fU fB t)
  | .binary a l r => fB a (treeFold fL fU fB l) (treeFold fL fU fB r)

def NiceTree.data {α : Type} : NiceTree α → α
  | .leaf a => a
  | .unary a _ => a
  | .binary a _ _ => a

def NiceTree.size {α : Type} : NiceTree α → Nat
  | .leaf _ => 1
  | .unary _ t => 1 + t.size
  | .binary _ l r => 1 + l.size + r.size

def NiceTree.depth {α : Type} : NiceTree α → Nat
  | .leaf _ => 0
  | .unary _ t => 1 + t.depth
  | .binary _ l r => 1 + Nat.max l.depth r.depth

def NiceTree.mapData {α α' : Type} (m : α → α') : NiceTree α → NiceTree α'
  | .leaf a => .leaf (m a)
  | .unary a t => .unary (m a) (t.mapData m)
  | .binary a l r => .binary (m a) (l.mapData m) (r.mapData m)

theorem treeFold_inv {α β : Type} (P : β → Prop)
    (fL : α → β) (fU : α → β → β) (fB : α → β → β → β)
    (h_leaf : ∀ a, P (fL a))
    (h_unary : ∀ a r, P r → P (fU a r))
    (h_binary : ∀ a r1 r2, P r1 → P r2 → P (fB a r1 r2))
    (t : NiceTree α) :
    P (treeFold fL fU fB t) := by
  induction t with
  | leaf a => exact h_leaf a
  | unary a t ih => exact h_unary a _ ih
  | binary a l r ihl ihr => exact h_binary a _ _ ihl ihr

theorem treeFold_inv_ext {α β : Type}
    (P : β → Prop) (Ext : β → β → Prop)
    (fL : α → β) (fU : α → β → β) (fB : α → β → β → β)
    (h_leaf : ∀ a, P (fL a))
    (h_unary : ∀ a r, P r → P (fU a r) ∧ Ext r (fU a r))
    (h_binary : ∀ a r1 r2, P r1 → P r2 →
      P (fB a r1 r2) ∧ Ext r1 (fB a r1 r2) ∧ Ext r2 (fB a r1 r2))
    (t : NiceTree α) :
    P (treeFold fL fU fB t) := by
  induction t with
  | leaf a => exact h_leaf a
  | unary a t ih => exact (h_unary a _ ih).1
  | binary a l r ihl ihr => exact (h_binary a _ _ ihl ihr).1

theorem treeFold_pair_inv {α β S : Type}
    (Inv : S → Prop)
    (fL : α → β × S) (fU : α → β × S → β × S)
    (fB : α → β × S → β × S → β × S)
    (h_leaf : ∀ a, Inv (fL a).2)
    (h_unary : ∀ a p, Inv p.2 → Inv (fU a p).2)
    (h_binary : ∀ a p1 p2, Inv p1.2 → Inv p2.2 → Inv (fB a p1 p2).2)
    (t : NiceTree α) :
    Inv (treeFold fL fU fB t).2 := by
  induction t with
  | leaf a => exact h_leaf a
  | unary a t ih => exact h_unary a _ ih
  | binary a l r ihl ihr => exact h_binary a _ _ ihl ihr

theorem treeFold_lower_bound {α : Type}
    (fL : α → Nat) (fU : α → Nat → Nat) (fB : α → Nat → Nat → Nat)
    (costL : α → Nat) (costU : α → Nat → Nat) (costB : α → Nat → Nat → Nat)
    (h_leaf : ∀ a, fL a ≤ costL a)
    (h_unary : ∀ a r c, r ≤ c → fU a r ≤ costU a c)
    (h_binary : ∀ a r1 r2 c1 c2, r1 ≤ c1 → r2 ≤ c2 → fB a r1 r2 ≤ costB a c1 c2)
    (t : NiceTree α) :
    treeFold fL fU fB t ≤ treeFold costL costU costB t := by
  induction t with
  | leaf a => exact h_leaf a
  | unary a t ih => exact h_unary a _ _ ih
  | binary a l r ihl ihr => exact h_binary a _ _ _ _ ihl ihr

theorem treeFold_mapData {α α' β : Type} (m : α → α')
    (fL : α' → β) (fU : α' → β → β) (fB : α' → β → β → β)
    (t : NiceTree α) :
    treeFold (fL ∘ m) (fU ∘ m) (fB ∘ m) t =
    treeFold fL fU fB (t.mapData m) := by
  induction t with
  | leaf a => rfl
  | unary a t ih => simp [treeFold, NiceTree.mapData, ih]
  | binary a l r ihl ihr => simp [treeFold, NiceTree.mapData, ihl, ihr]

theorem size_pos {α : Type} (t : NiceTree α) : 0 < t.size := by
  cases t <;> simp [NiceTree.size] <;> omega

end LambdaSat.Util.NiceTree
