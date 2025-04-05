import Mathlib

def DicksonSet {n : ℕ} (s : Set (Fin n → ℕ)) := {x ∈ s | IsMin x}

theorem DicksonSet_subset {n : ℕ} {s : Set (Fin n → ℕ)} : DicksonSet s ⊆ s := Set.sep_subset s _

theorem dickson {n : ℕ} (s : Set (Fin n → ℕ)) (h : s.Nonempty) :
    --                        v--- Change to (DicksonSet s).Nonempty, or Set.Nonempty (DicksonSet s)
    Finite (DicksonSet s) ∧ Nonempty (DicksonSet s) := by
  classical
  induction n with
  | zero =>
    simp only [nonempty_subtype, Fin.exists_fin_zero_pi]
    exact ⟨Subtype.finite, ⟨Subsingleton.mem_iff_nonempty.mpr h, Subsingleton.isMin finZeroElim⟩⟩
  | succ n ih =>
    let x := Fin.init '' s
    let ⟨x_fin, x_nonempty⟩ := ih x <| Set.Nonempty.image Fin.init h
    have hx : ∀ a ∈ DicksonSet x, ∃ b ∈ s, Fin.init b = a := by
      intro a ah
      rw [<- Set.mem_image]
      exact DicksonSet_subset ah
    choose f fh using hx
    let w := Set.Finite.toFinset x_fin
    let g : (Fin n → ℕ) → ℕ := fun y =>
      if h : y ∈ DicksonSet x then
        f y h (n + 1)
      else
        0
    let v := Finset.image g w
    have : ∃ α : ℕ, v.max = α := Finset.max_of_nonempty (by
      refine Finset.image_nonempty.mpr ?_
      refine (Set.Finite.toFinset_nonempty x_fin).mpr ?_
      exact Set.Nonempty.of_subtype
    )
    obtain ⟨v2, hv2⟩ := this
    sorry
