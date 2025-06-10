/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncLE
import Appendix.Mathlib.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation

Addendum to the mathlib file.

-/

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

section

variable [HasZeroObject C]

lemma isIso_ιTruncLE_f (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.ιTruncLE e).f (e.f i)) := by
  rw [← isIso_op_iff]
  exact K.op.isIso_πTruncGE_f e.op i hi

end

end HomologicalComplex
