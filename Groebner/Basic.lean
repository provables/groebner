import Mathlib

open MvPolynomial MonomialOrder

noncomputable section

variable {R : Type*} [CommSemiring R] {σ : Type*} (m : MonomialOrder σ)

/- First attempt:
Initial monomial as a polynomial. Simple definition, but we cannot compare the results of
this function via the monomial order, because the order doesn't extend to polynomials.
-/
def initialMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=
  letI := Classical.dec (f = 0)
  if f = 0 then
    0
  else
    monomial (m.degree f) 1

/- Second attempt:
Just return the initial monomial as σ →₀ ℕ . The inconvenience is that we need to use `monomial`
in every place that we want a polynomial, but now we can at least compare them.

It matches some theorems in the file `MvPolynomial.Ideal`.

It could be cool to definae some coercions, since there is a natural injection from monomials to
polynomials.
-/
def initialMonomial2 (f : MvPolynomial σ R) : σ →₀ ℕ := m.degree f

/- This coercion seems to be working, see `prod_initial_of_prod2` -/
instance : Coe (σ →₀ ℕ) (MvPolynomial σ R) where
  coe m := monomial m 1

theorem initial_eq_zero_of_zero : initialMonomial m 0 = (0 : MvPolynomial σ R) := by
  unfold initialMonomial
  simp only [↓reduceIte]

theorem prod_initial_of_prod (f g : MvPolynomial σ R) :
    initialMonomial m (f * g) = (initialMonomial m f) * (initialMonomial m g) := by
  sorry

theorem prod_initial_of_prod2 (f g : MvPolynomial σ R) :
    ((initialMonomial2 m (f * g)) : MvPolynomial σ ℝ) = initialMonomial2 m f * initialMonomial2 m g := by
  sorry

/- Working, if using `initialMonomial2` -/
theorem sum_initial_le_max (f g : MvPolynomial σ R) :
    m.toSyn (initialMonomial2 m (f + g)) ≤
      m.toSyn (initialMonomial2 m f) ⊔ m.toSyn (initialMonomial2 m g) := by
  unfold initialMonomial2
  exact degree_add_le

noncomputable def initialCoeff (f : MvPolynomial σ R) : R :=
  f.leadingCoeff m.toSyn

noncomputable def initialIdeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span { initialMonomial m f | f ∈ I }

/- Really need to use `f ≠ 0` in this definition, but that matches the book -/
noncomputable def initialIdeal2 (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span { g | ∃ f ∈ I, f ≠ 0 ∧ monomial (initialMonomial2 m f) 1 = g }

/-
An alternative definition of Monomials, by converting the aditive structure of σ →₀ ℕ into
a multiplicative one.
-/
abbrev Monomial σ := Multiplicative (σ →₀ ℕ)

/-
We define a monoid morphism which is injective, i.e., the usual embedding of monomials
into polynomials.
-/
def toMvPolynomial : Monomial σ →* MvPolynomial σ R where
  toFun m := monomial m 1
  map_one' := rfl
  map_mul' := by
    dsimp only [OneHom.toFun_eq_coe, OneHom.coe_mk]
    intro x y
    simp only [monomial_mul]
    congr
    ring

theorem toMvPolynomial_injective [Nontrivial R] :
    Function.Injective (toMvPolynomial : Monomial σ →* MvPolynomial σ R) :=
  monomial_left_injective one_ne_zero

instance : Coe (σ →₀ ℕ) (Monomial σ) where
  coe f := Multiplicative.ofAdd f

instance : Coe (Monomial σ) (σ →₀ ℕ) where
  coe m := Multiplicative.toAdd m

instance : Coe (Monomial σ) (MvPolynomial σ R) where
  coe := toMvPolynomial

structure OrderedMonomial (m : MonomialOrder σ) where
  toMonomial : Monomial σ

instance : Coe (Monomial σ) (OrderedMonomial m) where
  coe m := ⟨m⟩

instance : LE (OrderedMonomial m) where
  le u v := u.toMonomial ≼[m] v.toMonomial

def IsMonomial (f : MvPolynomial σ R) := ∃ m : Monomial σ, f = m

theorem IsMonomial_iff_support [DecidableEq σ] [DecidableEq R] [Nontrivial R]
    (f : MvPolynomial σ R) : IsMonomial f ↔ ∃ m : Monomial σ, f.support = {m} ∧ coeff m f = 1 := by
  constructor
  · rintro ⟨m, hm⟩
    use m
    simp [toMvPolynomial] at hm
    simp [hm, support_monomial, reduceIte]
  · rintro ⟨m, ⟨hml, hmr⟩⟩
    use m
    simp [toMvPolynomial]
    ext x
    simp [hml]
    by_cases h : m = x
    · simp [h, reduceIte]
      rwa [<- h]
    · simp [h]
      apply not_mem_support_iff.mp
      by_contra hx
      rw [hml] at hx
      exact h <| (Finset.eq_of_mem_singleton hx).symm

noncomputable def MonomialIdealOf (S: Set (Monomial σ)) (R : Type*) [CommSemiring R] :=
  Ideal.span {(g : MvPolynomial σ R) | g ∈ S}

noncomputable def IsMonomialIdeal (I : Ideal (MvPolynomial σ R)) : Prop :=
  ∃ S : Set (Monomial σ), MonomialIdealOf S R = I

theorem monIdeal_of (S : Set (Monomial σ)) : IsMonomialIdeal (MonomialIdealOf S R) := by
  use S

theorem IsMonomialIdeal_iff_MvPolynomial_span (I : Ideal (MvPolynomial σ R)) :
  IsMonomialIdeal I ↔
    ∃ S : Set (MvPolynomial σ R), (∀ p ∈ S, IsMonomial p) ∧ Ideal.span S = I := by
  constructor
  · rintro ⟨S, hS⟩
    use {(m : MvPolynomial σ R) | m ∈ S}
    constructor
    · rintro p ⟨m, hm⟩
      use m
      exact hm.right.symm
    · rw [← hS]
      rfl
  · rintro ⟨S, hS⟩
    let S' := {(m : Monomial σ) | ∃ f ∈ S, f = m}
    use S'
    rw [<- hS.right]
    unfold MonomialIdealOf S'
    have : {x | ∃ g ∈ {m | ∃ f ∈ S, f = toMvPolynomial m}, toMvPolynomial g = x} = S := by
      ext x
      constructor
      · rintro ⟨x, ⟨hxl, hxr⟩⟩
        obtain ⟨m, hm⟩ := hxl
        rw [<- hxr, <- hm.right]
        exact hm.left
      · intro hx
        obtain ⟨m, hm⟩ := hS.left x hx
        use m
        constructor
        · use x
        · exact hm.symm
    rw [this]

theorem monomialIdealOf_sub (S : Set (Monomial σ)) (T : Set (Monomial σ))
    (h : S ⊆ T) : MonomialIdealOf S R ≤ MonomialIdealOf T R := by
  unfold MonomialIdealOf
  have sub : {x : MvPolynomial σ R | ∃ g ∈ S, g = x} ⊆ {y | ∃ g ∈ T, g = y} := by
    intro a ha
    obtain ⟨g, hg⟩ := ha
    use g
    exact ⟨h hg.left, hg.right⟩
  exact Ideal.span_mono sub

/-
The regular monomial X^n, for n : σ
-/
def X (n : σ) : Monomial σ := Finsupp.single n 1

example (n : σ): IsMonomialIdeal (MonomialIdealOf {_root_.X n} R) := monIdeal_of {_root_.X n}

theorem supp_of_monomial [nt: Nontrivial R] (x : Monomial σ) :
    x ∈ (toMvPolynomial x: MvPolynomial σ R).support := by
  classical
  simp [toMvPolynomial]
  rw [support_monomial]
  split_ifs with hf
  · simp
    exact one_ne_zero hf
  · simp



theorem monomialIdeal_iff [nt: Nontrivial R] (I: Ideal (MvPolynomial σ R)) :
    IsMonomialIdeal I ↔ I = MonomialIdealOf { m | ∃ f ∈ I, m ∈ f.support} R := by
  constructor
  · intro hI
    obtain ⟨S, hS⟩ := hI
    let A := { m | ∃ f ∈ I, m ∈ f.support }
    have sub : S ⊆ A := by
      rw [Set.subset_def]
      intro x hx
      have xI : (x: MvPolynomial σ R) ∈ I := by
        rw[← hS]
        apply Ideal.subset_span
        use x
      use (x: MvPolynomial σ R)
      constructor
      · exact xI
      · exact supp_of_monomial x
    rw [le_antisymm_iff]
    constructor
    · nth_rw 1 [← hS]
      apply monomialIdealOf_sub
      exact sub

    -- claim: if m ∈ A, then m ∈ f.support, some f ∈ I.
    --        write f = ∑ r_i s_i, with s_i ∈ S.
    --        then f.support = ∪ s_i and thus m ∈ ∪ s_i



/-- Theorem 1.7 in Herzog -/
theorem monIdeal_iff_supp (I : Ideal (MvPolynomial σ R)) :
    IsMonomialIdeal I ↔ ∀ f ∈ I, {(m : MvPolynomial σ R) | m ∈ f.support} ⊆ I := by
  constructor
  · intro hI f hfI
    obtain ⟨S, hS⟩ := hI
    rw [<- hS] at hfI
    let S' : Set (MvPolynomial σ R):= { x | ∃ g ∈ S, toMvPolynomial g = x}
    let p (f : MvPolynomial σ R) (h : f ∈ Ideal.span S') : Prop :=
      {x | ∃ m ∈ f.support, (monomial m) (1 : R) = x} ⊆ I
    have mem : ∀ (x) (h : x ∈ S'), p x (Ideal.subset_span h) := by
      intro x hx
      unfold p
      intro a ha
      obtain ⟨ x1, ⟨ hx1l, hx1r⟩  ⟩ := ha
      have : a ∈ { x | ∃ g ∈ S, toMvPolynomial g = x} := by
        obtain ⟨ x2, hx2 ⟩ := hx
        use x2
        constructor
        · exact hx2.left
        · rw [<- hx1r]
          simp [toMvPolynomial] at hx2
          rw [<- hx2.right] at hx1l
          apply support_monomial_subset at hx1l
          let u := Finset.eq_of_mem_singleton hx1l
          rw [<- u]
          rfl
      rw [<- hS]
      exact Ideal.subset_span this
    have zero : p 0 (Ideal.zero_mem _) := by
      unfold p
      rw [MvPolynomial.support_zero]
      simp
    have add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Ideal.add_mem _ ‹_› ‹_›) := by
      sorry
    have smul : ∀ (a : MvPolynomial σ R) (x hx), p x hx → p (a * x)
        (Ideal.mul_mem_left _ _ ‹_›) := by
      sorry
    exact Submodule.span_induction mem zero add smul hfI
  · intro h
    whnf
    use {(m : Monomial σ) | ∃ f ∈ I, m ∈ f.support}
    ext y
    constructor
    · sorry
    · sorry

/-
The monomial X^n considered with the order m
-/
def Xord (m : MonomialOrder σ) (n : σ) : OrderedMonomial m := ⟨X n⟩
notation:80 "X[" n "," m "]" => Xord m n

theorem ordMon_le_iff_monomialOrder_le (u v : OrderedMonomial m) :
  u ≤ v ↔ u.toMonomial ≼[m] v.toMonomial := by rfl

theorem monomialOrder_le_iff_le (u v : Monomial σ) :
  u ≼[m] v ↔ (u : OrderedMonomial m) ≤ v := by rfl

/-
Divisibility in monomials is the same as in polynomials
-/
theorem monomial_dvd_iff_dvd [Nontrivial R] (u v : Monomial σ) :
    u ∣ v ↔ (u : MvPolynomial σ R) ∣ v := by
  constructor <;> intro h
  · rw [dvd_def] at h
    obtain ⟨c, hc⟩ := h
    rw [hc, map_mul]
    apply dvd_mul_right
  · unfold toMvPolynomial at h
    simp at h
    rw [le_iff_exists_add] at h
    exact h

/-
Divisibility in monomials is the pointwise order in functions σ →₀ ℕ
-/
theorem mon_dvd_iff_le (u v : Monomial σ) : u ∣ v ↔ u.toAdd ≤ v.toAdd := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [le_iff_exists_add]
    use c.toAdd
    exact hc
  · intro h
    rw [le_iff_exists_add] at h
    obtain ⟨c, hc⟩ := h
    use Multiplicative.ofAdd c
    exact hc

/-
The partial order in monomials is the divisibility partial order
-/
theorem le_iff_dvd (u v : Monomial σ) : u ≤ v ↔ u ∣ v := by
  constructor
  · exact fun _ => by rwa [mon_dvd_iff_le]
  · intro h
    rwa [mon_dvd_iff_le] at h

/-- Theorem 1.9 in Herzog -/
theorem dickson_lemma (hs : Finite σ) (s : Set (Monomial σ)) (h : Nonempty s) :
    Finite {x ∈ s | IsMin x} := by
  sorry

/-- Corollary 1.10 in Herzog -/
theorem finite_MonomialIdeal_of_MonomialIdeal
  (I : Ideal (MvPolynomial σ R))
  (S : Set (Monomial σ))
  (hI : MonomialIdealOf S R = I) :
    ∃ S' ⊆ S, Finite S' ∧ MonomialIdealOf S' R = I := by
  sorry

/-
Example: Y < X in the lexicographic order
-/
example : X[(1 : Fin 2),MonomialOrder.lex] ≤ X[0,_] := by
  refine (monomialOrder_le_iff_le _ _ _).mp ?_
  apply MonomialOrder.lex_le_iff.mpr
  unfold _root_.X
  exact Finsupp.Lex.single_le_iff.mpr <| Fin.zero_le 1

/-
Proposition 2.2.i in Herzog
-/
theorem le_of_div [Nontrivial R] (u v : Monomial σ) (h : (u : MvPolynomial σ R) ∣ v) :
    (u : OrderedMonomial m) ≤ v := by
  simp only [toMvPolynomial, MonoidHom.coe_mk, OneHom.coe_mk] at h
  rw [monomial_dvd_monomial] at h
  rcases h with (h1 | h2)
  · exfalso
    exact one_ne_zero h1
  · rw [<- monomialOrder_le_iff_le]
    exact m.toSyn_monotone h2
