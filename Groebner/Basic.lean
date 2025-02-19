import Mathlib

open MvPolynomial

variable {R : Type*} [CommSemiring R] {σ : Type*} (m : MonomialOrder σ)

noncomputable def initialMonomial (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) 1

#check initialMonomial MonomialOrder.degLex (X (⟨0, by simp⟩: Finset.range 1))
