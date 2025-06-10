/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.Embedding.IsSupported
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical truncation

Addendum to the mathlib file.

-/

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

section

variable [HasZeroObject C]

lemma isIso_πTruncGE_f (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.πTruncGE e).f (e.f i)) := by
  dsimp [πTruncGE]
  rw [e.isIso_liftExtend_f_iff _ _ rfl]
  dsimp
  rw [restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ _ rfl hi]
  dsimp
  infer_instance

end

end HomologicalComplex
