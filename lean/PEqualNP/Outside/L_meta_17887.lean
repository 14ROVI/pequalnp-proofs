import Mathlib.Combinatorics.SimpleGraph.Acyclic

theorem PEqualNP.Outside.L_meta_17887 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : SimpleGraph (Fin (x1 + x2))), (∀ (x6 x7 : Fin (x1 + x2)), x5.Adj x6 x7 ↔ ∃ x8 ∈ x3, x6 = Fin.castAdd x2 x8.1 ∧ x7 = Fin.natAdd x1 x8.2 ∨ x7 = Fin.castAdd x2 x8.1 ∧ x6 = Fin.natAdd x1 x8.2) → ¬x5.IsAcyclic → (∀ x8 ∈ x4, ∀ x10 ∈ x4, x8.1 = x10.1 → x8 = x10) → (∀ x9 ∈ x4, ∀ x11 ∈ x4, x9.2 = x11.2 → x9 = x11) → x4 ⊆ x3 → (∀ (x11 x12 : Fin x1) (x13 x14 : Fin x2), x11 ≠ x12 → x13 ≠ x14 → ¬((x11, x13) ∈ x3 ∧ (x11, x14) ∈ x3 ∧ (x12, x13) ∈ x3 ∧ (x12, x14) ∈ x3)) → (∀ x12 ∈ x3, ((∀ x14 ∈ x3, x14.1 = x12.1 → x14 = x12) ∨ ∀ x14 ∈ x3, x14.2 = x12.2 → x14 = x12) → (x3.erase x12).Nonempty → x12 ∈ x4) → ∃ x13 ∈ x3, x13 ∉ x4 := by
  intro m n edges matching G adj cyclic left right _ _ _
  by_contra! allMatched
  apply cyclic
  intro v walk cycle
  have unique {w z : Fin (m+n)} (hw : G.Adj v w) (hz : G.Adj v z) : w = z := by
    obtain ⟨e, he, hedir⟩ := (adj v w).mp hw
    obtain ⟨f, hf, hfdir⟩ := (adj v z).mp hz
    have disjoint (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
      intro h
      have hv := congrArg Fin.val h
      change i.val = m + j.val at hv
      omega
    rcases hedir with ⟨hv, rfl⟩ | ⟨rfl, hv⟩ <;>
      rcases hfdir with ⟨hv', rfl⟩ | ⟨rfl, hv'⟩
    · have eq := left e (allMatched e he) f (allMatched f hf)
          (by simpa using hv.symm.trans hv')
      rw [eq]
    · exact (disjoint _ _ (hv.symm.trans hv')).elim
    · exact (disjoint _ _ (hv'.symm.trans hv)).elim
    · have eq := right e (allMatched e he) f (allMatched f hf)
          (by simpa using hv.symm.trans hv')
      rw [eq]
  exact cycle.snd_ne_penultimate (unique (walk.adj_snd cycle.not_nil) (walk.adj_penultimate cycle.not_nil).symm)
