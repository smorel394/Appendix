/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Appendix.Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Properties of objects which hold for a zero object

Addendum to mathlib file.
-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

-- to be moved
lemma IsZero.of_full_of_faithful_of_isZero
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) (hX : IsZero (F.obj X)) :
    IsZero X := by
      have h : F.FullyFaithful := .ofFullyFaithful _
      constructor
      · intro Y
        have := (hX.unique_to (F.obj Y)).some
        exact ⟨h.homEquiv.unique⟩
      · intro Y
        have := (hX.unique_from (F.obj Y)).some
        exact ⟨h.homEquiv.unique⟩

namespace ObjectProperty

variable (P Q : ObjectProperty C)

instance [HasZeroObject C] : (⊤ : ObjectProperty C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by simp⟩

instance [HasZeroObject C] : ContainsZero (IsZero (C := C)) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩

instance [P.ContainsZero] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : (P.map F).ContainsZero where
  exists_zero := by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨F.obj Z, F.map_isZero h₁, P.prop_map_obj F h₂⟩

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : D ⥤ C) [F.PreservesZeroMorphisms] [HasZeroObject D] :
    (P.inverseImage F).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero D, P.prop_of_isZero (F.map_isZero (isZero_zero D))⟩

instance [P.ContainsZero] : P.isoClosure.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_isoClosure _ hP⟩

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [Q.ContainsZero] :
    (P ⊓ Q).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.prop_of_isZero hZ, hQ⟩

instance [P.ContainsZero] : P.op.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨op Z, hZ.op, mem⟩

instance (P : ObjectProperty Cᵒᵖ) [P.ContainsZero] : P.unop.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨Z.unop, hZ.unop, mem⟩

instance [P.ContainsZero] : HasZeroObject P.FullSubcategory where
  zero := by
    obtain ⟨X, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨_, IsZero.of_full_of_faithful_of_isZero P.ι ⟨X, h₂⟩ h₁⟩

end ObjectProperty

end CategoryTheory
