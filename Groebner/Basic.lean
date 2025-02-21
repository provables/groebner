import Mathlib

open MvPolynomial MonomialOrder

variable {R : Type*} [CommSemiring R] {σ : Type*} (m : MonomialOrder σ)

noncomputable def initialMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=
  letI := Classical.dec (f = 0)
  if f = 0 then
    0
  else
    monomial (m.degree f) 1

theorem initial_eq_zero_of_zero : initialMonomial m 0 = (0 : MvPolynomial σ R) := by
  unfold initialMonomial
  simp only [↓reduceIte]

theorem prod_initial_of_prod (f g : MvPolynomial σ R) :
    initialMonomial m (f * g) = (initialMonomial m f) * (initialMonomial m g) := by
  sorry

/- Not working. Need to figure out how to do `max` with the monomial order -/
theorem sum_initial_le_max (f g : MvPolynomial σ R) :
    initialMonomial m (f + g) ≤ sup (initialMonomial m f) (initialMonomial m g) := by
  sorry

noncomputable def initialCoeff (f : MvPolynomial σ R) : R :=
  f.leadingCoeff m.toSyn

noncomputable def initialIdeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  Ideal.span { initialMonomial m f | f ∈ I }

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
