import Mathlib

def DicksonSet {n : ℕ} (s : Set (Fin n → ℕ)) := {x ∈ s | IsMin x}

theorem DicksonSet_subset {n : ℕ} {s : Set (Fin n → ℕ)} : DicksonSet s ⊆ s := Set.sep_subset s _

#check Set.not_nonempty_empty
#check Set.eq_empty_or_nonempty
#check Set.nonempty_iff_ne_empty
#check Set.Finite.sep
#check @Set.Finite

example (P Q : Prop) : P ∨ Q → ¬Q → P := fun pq nq ↦
  Or.casesOn pq (fun h1 ↦ h1) fun h2 ↦ False.elim (nq h2)

theorem dickson {n : ℕ} (s : Set (Fin n → ℕ)) (h : s.Nonempty) :
    (DicksonSet s).Finite ∧ (DicksonSet s).Nonempty := by
  classical
  induction n with
  | zero =>
    constructor
    · exact Set.toFinite (DicksonSet s)
    · use ⊥
      exact ⟨Subsingleton.mem_iff_nonempty.mpr h, isMin_bot⟩
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
    have : ∃ α : ℕ, v.max = α := Finset.max_of_nonempty <|
      Finset.image_nonempty.mpr <| (Set.Finite.toFinset_nonempty x_fin).mpr <|
      x_nonempty
    obtain ⟨v2, hv2⟩ := this
    let nset : Fin (v2 + 1) → Set (Fin n → ℕ) := fun m => {x | Fin.snoc x m ∈ s}
    have : ∀ b : Fin (v2 + 1), nset b = ∅  ∨ (DicksonSet (nset b)).Finite := by
      intro b
      by_cases emp : nset b = ∅
      · exact Or.inl emp
      · push_neg at emp
        exact Or.inr (ih (nset b) emp).left
    let nset_fin : Fin (v2 + 1) → Set (Fin n → ℕ) := fun b =>
      if hne : (nset b).Nonempty then
        DicksonSet (nset b)
      else
        ∅
    let f : Fin (v2 + 1) → (Fin n → ℕ) → (Fin (n + 1) → ℕ) := fun b x => Fin.snoc x b
    let nset_ext : Fin (v2 + 1) → Set (Fin (n + 1) → ℕ) := fun b => (f b) '' (nset_fin b)
    have : ∀ b : Fin (v2 + 1), (nset_ext b).Finite := by
      intro b
      unfold nset_ext
      apply Set.Finite.image
      unfold nset_fin
      by_cases hb : nset b = ∅
      · simp [hb]
      · push_neg at hb
        simp [hb]
        exact Or.resolve_left (this b) (Set.nonempty_iff_ne_empty.mp hb)
    sorry
