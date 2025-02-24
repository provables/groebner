import Mathlib

open MvPolynomial MonomialOrder

variable {R : Type*} [CommSemiring R] [Nontrivial R] {σ : Type*} (m : MonomialOrder σ)

/- First attempt:
Initial monomial as a polynomial. Simple definition, but we cannot compare the results of
this function via the monomial order, because the order doesn't extend to polynomials.
-/
noncomputable def initialMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=
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
noncomputable def initialMonomial2 (f : MvPolynomial σ R) : σ →₀ ℕ := m.degree f

/- This coercion seems to be working, see `prod_initial_of_prod2` -/
noncomputable instance : Coe (σ →₀ ℕ) (MvPolynomial σ R) where
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
noncomputable def toMvPolynomial : Monomial σ →* MvPolynomial σ R where
  toFun m := monomial m 1
  map_one' := rfl
  map_mul' := by
    dsimp only [OneHom.toFun_eq_coe, OneHom.coe_mk]
    intro x y
    simp only [monomial_mul]
    congr
    ring

theorem toMvPolynomial_injective :
    Function.Injective (toMvPolynomial : Monomial σ →* MvPolynomial σ R) := by
  apply monomial_left_injective
  exact one_ne_zero
