/-
  LambdaSat — add_node_triple (aux file for F8S3)
  Proves: EGraph.add preserves CV + PMI + SHI + HCB triple.
-/
import LambdaSat.SemanticSpec

open LambdaSat UnionFind

namespace LambdaSat

variable {Op : Type} [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [NodeOps Op] [DecidableEq Op] [Repr Op] [Inhabited Op]
  {Val : Type} [NodeSemantics Op Val] [Inhabited Val]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 6400000 in
theorem add_node_triple (g : EGraph Op) (node : ENode Op) (env : Nat → Val) (v : EClassId → Val)
    (hv : ConsistentValuation g env v) (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v) (hhcb : HashconsChildrenBounded g)
    (hbnd : ∀ c ∈ node.children, c < g.unionFind.parent.size) :
    ∃ v', ConsistentValuation (g.add node).2 env v' ∧
      PostMergeInvariant (g.add node).2 ∧
      SemanticHashconsInv (g.add node).2 env v' ∧
      HashconsChildrenBounded (g.add node).2 ∧
      (g.add node).1 < (g.add node).2.unionFind.parent.size ∧
      g.unionFind.parent.size ≤ (g.add node).2.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      v' (root (g.add node).2.unionFind (g.add node).1) = NodeEval node env v' := by
  simp only [EGraph.add]
  split
  · -- HIT CASE
    rename_i existingId hm
    show ∃ v', ConsistentValuation ((g.canonicalize node).2.find existingId).2 env v' ∧
      PostMergeInvariant ((g.canonicalize node).2.find existingId).2 ∧
      SemanticHashconsInv ((g.canonicalize node).2.find existingId).2 env v' ∧
      HashconsChildrenBounded ((g.canonicalize node).2.find existingId).2 ∧
      ((g.canonicalize node).2.find existingId).1 <
        ((g.canonicalize node).2.find existingId).2.unionFind.parent.size ∧
      g.unionFind.parent.size ≤
        ((g.canonicalize node).2.find existingId).2.unionFind.parent.size ∧
      (∀ i, i < g.unionFind.parent.size → v' i = v i) ∧
      v' (root ((g.canonicalize node).2.find existingId).2.unionFind
        ((g.canonicalize node).2.find existingId).1) = NodeEval node env v'
    have hwf := hpmi.uf_wf
    have hwf1 := canonicalize_uf_wf g node hwf
    rw [canonicalize_hashcons] at hm
    have hev := hpmi.hashcons_entries_valid _ _ hm
    refine ⟨v,
      find_consistent _ _ env v (canonicalize_consistent g node env v hv hwf) hwf1,
      ⟨egraph_find_uf_wf _ _ hwf1,
       fun cid cls hget n hn c hc => by
         rw [egraph_find_classes, canonicalize_classes] at hget
         rw [egraph_find_uf_size, canonicalize_uf_size]; exact hpmi.children_bounded cid cls hget n hn c hc,
       fun n nid hget => by
         rw [egraph_find_hashcons, canonicalize_hashcons] at hget
         rw [egraph_find_uf_size, canonicalize_uf_size]; exact hpmi.hashcons_entries_valid n nid hget,
       fun cid hcont => by
         rw [egraph_find_classes, canonicalize_classes] at hcont
         rw [egraph_find_uf_size, canonicalize_uf_size]; exact hpmi.classes_entries_valid cid hcont⟩,
      ?_, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
    · intro nd nid hget; rw [egraph_find_hashcons, canonicalize_hashcons] at hget
      rw [hshi nd nid hget]; congr 1
      exact ((egraph_find_preserves_roots _ existingId nid hwf1).trans
        (canonicalize_preserves_roots g node hwf nid)).symm
    · intro nd nid hget c hc; rw [egraph_find_hashcons, canonicalize_hashcons] at hget
      rw [egraph_find_uf_size, canonicalize_uf_size]; exact hhcb nd nid hget c hc
    · rw [egraph_find_fst, egraph_find_uf_size]; rw [← canonicalize_uf_size g node] at hev
      simp only [root]; exact rootD_bounded hwf1.1 hev
    · rw [egraph_find_uf_size, canonicalize_uf_size]; exact Nat.le_refl _
    · rw [egraph_find_fst]
      have hbnd1 : existingId < (g.canonicalize node).2.unionFind.parent.size := by
        rw [canonicalize_uf_size]; exact hev
      have hroot_eq : root ((g.canonicalize node).2.find existingId).2.unionFind
          (root (g.canonicalize node).2.unionFind existingId) = root g.unionFind existingId := by
        rw [egraph_find_preserves_roots _ existingId _ hwf1,
            root_idempotent _ existingId hwf1 hbnd1,
            canonicalize_preserves_roots g node hwf]
      rw [hroot_eq, ← nodeEval_canonical g node env v hv.1 hwf hbnd]; exact (hshi _ _ hm).symm
  · -- MISS CASE
    rename_i hmiss
    simp only [UnionFind.add]
    have hwf := hpmi.uf_wf
    have hwf1 := canonicalize_uf_wf g node hwf
    have hcusz := canonicalize_uf_size g node
    have hroot_self : root ⟨(g.canonicalize node).2.unionFind.parent.push
        (g.canonicalize node).2.unionFind.parent.size⟩
        (g.canonicalize node).2.unionFind.parent.size =
        (g.canonicalize node).2.unionFind.parent.size := by
      simp only [root]
      exact rootD_of_isRoot ⟨by simp [Array.size_push], Array.getElem_push_eq⟩
        (by simp [Array.size_push])
    refine ⟨fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i,
      ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- UF-consistency
      have hroots : ∀ k, root ⟨(g.canonicalize node).2.unionFind.parent.push
            (g.canonicalize node).2.unionFind.parent.size⟩ k = root g.unionFind k :=
        fun k => (root_push_all_eq hwf1 k).trans (canonicalize_preserves_roots g node hwf k)
      have hrootN : root g.unionFind g.unionFind.parent.size = g.unionFind.parent.size :=
        root_oob g.unionFind _ (Nat.lt_irrefl _)
      have hroot_bnd : ∀ j, j < g.unionFind.parent.size → root g.unionFind j <
          g.unionFind.parent.size := fun j hj => by simp only [root]; exact rootD_bounded hwf.1 hj
      intro i j hij; simp only []
      rw [hroots, hroots] at hij
      by_cases hi : i = g.unionFind.parent.size
      · subst hi; by_cases hj : j = g.unionFind.parent.size
        · subst hj; rfl
        · exfalso; rw [hrootN] at hij
          by_cases hjb : j < g.unionFind.parent.size
          · exact Nat.ne_of_lt (hroot_bnd j hjb) hij.symm
          · exact hj (by rw [root_oob g.unionFind j hjb] at hij; exact hij.symm)
      · by_cases hj : j = g.unionFind.parent.size
        · subst hj; exfalso; rw [hrootN] at hij
          by_cases hib : i < g.unionFind.parent.size
          · exact Nat.ne_of_lt (hroot_bnd i hib) hij
          · exact hi (by rw [root_oob g.unionFind i hib] at hij; exact hij)
        · simp only [hi, hj, ite_false]; exact hv.1 i j hij
    · -- Node-consistency
      intro classId eclass hcls nd hmem; simp only []
      by_cases hid : g.unionFind.parent.size = classId
      · subst hid
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
        split at hcls
        · simp at hcls; subst hcls; simp [EClass.singleton] at hmem; rw [hmem]
          simp only [ite_true]
          rw [nodeEval_children_eq (g.canonicalize node).1 env _ v
            (fun c hc => by
              show (if c = g.unionFind.parent.size then _ else _) = _
              rw [if_neg (Nat.ne_of_lt (hcusz ▸ canonicalize_output_bounded g node hwf hbnd c hc))])]
          exact nodeEval_canonical g node env v hv.1 hwf hbnd
        · rename_i hne; simp [hcusz] at hne
      · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hcls
        split at hcls
        · rename_i heq; simp at heq; rw [hcusz] at heq; exact absurd heq hid
        · rw [canonicalize_classes] at hcls
          have hcls' : g.classes.get? classId = some eclass := by
            rw [Std.HashMap.get?_eq_getElem?]; exact hcls
          simp only [show classId ≠ g.unionFind.parent.size from Ne.symm hid, ite_false]
          rw [nodeEval_children_eq nd env _ v
            (fun c hc => by
              show (if c = g.unionFind.parent.size then _ else _) = _
              rw [if_neg (Nat.ne_of_lt (hpmi.children_bounded classId eclass hcls' nd hmem c hc))])]
          exact hv.2 classId eclass hcls' nd hmem
    · -- PMI.uf_wf
      exact add_wf _ hwf1
    · -- PMI.children_bounded
      intro cid cls hget n hn c hc
      simp only [Array.size_push]
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hget
      split at hget
      · rename_i heq; simp at heq; subst heq; simp [EClass.singleton] at hget; subst hget
        simp at hn; rw [hn] at hc
        exact Nat.lt_succ_of_lt (hcusz ▸ canonicalize_output_bounded g node hwf hbnd c hc)
      · rw [canonicalize_classes] at hget
        exact Nat.lt_succ_of_lt (hcusz ▸ hpmi.children_bounded cid cls
          (by rw [Std.HashMap.get?_eq_getElem?]; exact hget) n hn c hc)
    · -- PMI.hashcons_entries_valid
      intro n nid hget; simp only [Array.size_push]
      by_cases hcn : (g.canonicalize node).1 = n
      · subst hcn; rw [hashcons_get?_insert_self] at hget
        simp at hget; subst hget; exact Nat.lt_succ_of_le (Nat.le_refl _)
      · rw [hashcons_get?_insert_ne _ _ _ _ hcn, canonicalize_hashcons] at hget
        exact Nat.lt_succ_of_lt (hcusz ▸ hpmi.hashcons_entries_valid n nid hget)
    · -- PMI.classes_entries_valid
      intro cid hcont; simp only [Array.size_push]
      rw [Std.HashMap.contains_insert] at hcont
      by_cases h : cid = (g.canonicalize node).2.unionFind.parent.size
      · rw [h]; exact Nat.lt_succ_of_le (Nat.le_refl _)
      · simp [BEq.beq] at hcont
        rcases hcont with rfl | hcont'
        · exact absurd rfl h
        · rw [canonicalize_classes] at hcont'
          exact Nat.lt_succ_of_lt (hcusz ▸ hpmi.classes_entries_valid cid
            (Std.HashMap.mem_iff_contains.mp hcont'))
    · -- SHI
      intro nd nid hget; simp only [] at hget
      by_cases hcn : (g.canonicalize node).1 = nd
      · -- New entry
        subst hcn; rw [hashcons_get?_insert_self] at hget; simp at hget; subst hget
        show NodeEval (g.canonicalize node).1 env _ =
          (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i)
            (root ⟨(g.canonicalize node).2.unionFind.parent.push
              (g.canonicalize node).2.unionFind.parent.size⟩
              (g.canonicalize node).2.unionFind.parent.size)
        rw [hroot_self, hcusz]; simp only [ite_true]
        rw [nodeEval_children_eq (g.canonicalize node).1 env _ v
          (fun c hc => by
            show (if c = g.unionFind.parent.size then _ else _) = _
            rw [if_neg (Nat.ne_of_lt (hcusz ▸ canonicalize_output_bounded g node hwf hbnd c hc))])]
        exact nodeEval_canonical g node env v hv.1 hwf hbnd
      · -- Old entry
        rw [hashcons_get?_insert_ne _ _ _ _ hcn, canonicalize_hashcons] at hget
        have hchi_bnd := hhcb nd nid hget
        rw [nodeEval_children_eq nd env _ v (fun c hc => by
            show (if c = g.unionFind.parent.size then _ else _) = _
            rw [if_neg (Nat.ne_of_lt (hchi_bnd c hc))])]
        have hroot_old : root ⟨(g.canonicalize node).2.unionFind.parent.push
            (g.canonicalize node).2.unionFind.parent.size⟩ nid = root g.unionFind nid :=
          (root_push_all_eq hwf1 nid).trans (canonicalize_preserves_roots g node hwf nid)
        have hroot_bnd : root g.unionFind nid < g.unionFind.parent.size := by
          simp only [root]; exact rootD_bounded hwf.1 (hpmi.hashcons_entries_valid nd nid hget)
        -- Goal: NodeEval nd env v = v' (root newUF nid)
        -- v' (root newUF nid) = v' (root g.uf nid) [by hroot_old]
        -- = v (root g.uf nid) [by if_neg since root < size]
        -- = NodeEval nd env v [by hshi]
        have heval : (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i)
            (root ⟨(g.canonicalize node).2.unionFind.parent.push
              (g.canonicalize node).2.unionFind.parent.size⟩ nid) = v (root g.unionFind nid) := by
          rw [hroot_old]
          show (if root g.unionFind nid = g.unionFind.parent.size then _ else _) = _
          rw [if_neg (Nat.ne_of_lt hroot_bnd)]
        rw [heval]; exact hshi nd nid hget
    · -- HCB
      intro nd nid hget c hc; simp only [Array.size_push]; simp only [] at hget
      by_cases hcn : (g.canonicalize node).1 = nd
      · subst hcn; rw [hashcons_get?_insert_self] at hget
        simp at hget; subst hget
        exact Nat.lt_succ_of_lt (hcusz ▸ canonicalize_output_bounded g node hwf hbnd c hc)
      · rw [hashcons_get?_insert_ne _ _ _ _ hcn, canonicalize_hashcons] at hget
        exact Nat.lt_succ_of_lt (hcusz ▸ hhcb nd nid hget c hc)
    · -- ID bounded
      rw [Array.size_push]; exact Nat.lt_succ_of_le (Nat.le_refl _)
    · -- Size monotonic
      rw [Array.size_push, hcusz]; exact Nat.le_succ _
    · -- Forward preservation
      intro i hi
      show (if i = g.unionFind.parent.size then _ else _) = _
      rw [if_neg (Nat.ne_of_lt hi)]
    · -- Value
      show (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i)
          (root ⟨(g.canonicalize node).2.unionFind.parent.push
            (g.canonicalize node).2.unionFind.parent.size⟩
            (g.canonicalize node).2.unionFind.parent.size) =
        NodeEval node env (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i)
      rw [hroot_self, hcusz]; simp only [ite_true]
      exact (nodeEval_children_eq node env
        (fun i => if i = g.unionFind.parent.size then NodeEval node env v else v i) v
        (fun c hc => by
          show (if c = g.unionFind.parent.size then _ else _) = _
          rw [if_neg (Nat.ne_of_lt (hbnd c hc))])).symm

omit [DecidableEq Op] [Repr Op] [Inhabited Op] in
/-- merge preserves HashconsChildrenBounded: merge doesn't touch hashcons or uf.parent.size. -/
theorem merge_preserves_hcb (g : EGraph Op) (a b : EClassId)
    (hhcb : HashconsChildrenBounded g) :
    HashconsChildrenBounded (g.merge a b) := by
  intro nd nid hget c hc
  rw [merge_hashcons] at hget
  rw [merge_uf_size]
  exact hhcb nd nid hget c hc

omit [DecidableEq Op] [Repr Op] [Inhabited Op] [NodeSemantics Op Val] [Inhabited Val] in
/-- HashconsChildrenBounded holds vacuously for the empty e-graph. -/
theorem empty_hcb [Inhabited Val] :
    HashconsChildrenBounded (Op := Op) EGraph.empty := by
  intro nd id h
  simp [EGraph.empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_nil] at h

end LambdaSat
