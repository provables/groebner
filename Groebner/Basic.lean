import Mathlib

open MvPolynomial MonomialOrder

variable {R : Type*} [CommSemiring R] {σ : Type*} (m : MonomialOrder σ)

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

theorem initial_eq_zero_of_zero : initialMonomial m 0 = (0 : MvPolynomial σ R) := by
  unfold initialMonomial
  simp only [↓reduceIte]

theorem prod_initial_of_prod (f g : MvPolynomial σ R) :
    initialMonomial m (f * g) = (initialMonomial m f) * (initialMonomial m g) := by
  sorry

theorem prod_initial_of_prod2 (f g : MvPolynomial σ R) :
    monomial (initialMonomial2 m (f * g)) 1 = monomial (initialMonomial2 m f) 1 * monomial (initialMonomial2 m g) 1 := by
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

#check IsNoetherian

/- Playground -/

#check em
#check Classical.propDecidable

noncomputable def myVars [DecidableEq σ] (p : MvPolynomial σ R) : Finset σ :=
  p.degrees.toFinset

#loogle MvPolynomial, "leadingCoeff"

#check Module.Free.of_basis
#check initialMonomial MonomialOrder.degLex (X (0 : Fin 1))

#check Polynomial.leadingCoeff
#check Polynomial.leadingCoeff_C
#check Ideal.FG
#check Ideal.span

variable (p : MvPolynomial σ ℤ) (n : σ)
#check initialCoeff m p
#check (initialCoeff m p) • (initialMonomial m p)

#check p.leadingCoeff m.toSyn

noncomputable def X : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0
noncomputable def Y : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1
noncomputable def f := (MvPolynomial.C (1 / 2)) * ((X + Y) ^ 2 + (MvPolynomial.C 3) * X + Y)
