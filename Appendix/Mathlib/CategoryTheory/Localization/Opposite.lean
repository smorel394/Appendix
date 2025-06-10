/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Equivalence

/-!

# Localization of the opposite category

Addendum to the mathlib file.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {W : MorphismProperty C}

variable (L W)

namespace Functor

lemma isLocalization_iff_op :
    L.IsLocalization W ↔ L.op.IsLocalization W.op := by
  constructor
  · intro
    infer_instance
  · intro
    letI : CatCommSq (opOpEquivalence C).functor L.op.op L (opOpEquivalence D).functor :=
      ⟨Iso.refl _⟩
    refine Functor.IsLocalization.of_equivalences (L.op.op) W.op.op L W
      (opOpEquivalence C) (opOpEquivalence D) ?_ ?_
    · intro X Y f hf
      exact MorphismProperty.le_isoClosure _ _ hf
    · intro X Y f hf
      have := Localization.inverts L.op W.op f.op hf
      change IsIso (asIso (L.op.map f.op)).unop.hom
      infer_instance

end Functor

end CategoryTheory
