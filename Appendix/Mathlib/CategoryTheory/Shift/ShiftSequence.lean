/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! Sequences of functors from a category equipped with a shift

Addendum to the mathlib file.

-/

open CategoryTheory Category ZeroObject Limits

variable {C A : Type*} [Category C] [Category A] (F : C ⥤ A)
  (M : Type*) [AddMonoid M] [HasShift C M]
  {G : Type*} [AddGroup G] [HasShift C G]

namespace CategoryTheory

namespace Functor

section Hom

variable (G : C ⥤ A) [F.ShiftSequence M] [G.ShiftSequence M]

/-- Morphisms of `ShiftSequence`s.
-/
structure ShiftSequenceHom where
  app : (n : M) → (F.shift n ⟶ G.shift n)
  compatibility : ∀ (n a a' : M) (h : n + a = a'),
      whiskerLeft (shiftFunctor C n) (app a) ≫ (G.shiftIso n a a' h).hom =
      (F.shiftIso n a a' h).hom ≫ app a'

/-- Isomorphisms of `ShiftSequence`s.
-/
structure ShiftSequenceIso where
  app : (n : M) → (F.shift n ≅ G.shift n)
  compatibility : ∀ (n a a' : M) (h : n + a = a'),
      whiskerLeft (shiftFunctor C n) (app a).hom ≫ (G.shiftIso n a a' h).hom =
      (F.shiftIso n a a' h).hom ≫ (app a').hom

/-- Constructing a `Hom` between the tautological `ShiftSequence`s from a natural transformation.
-/
noncomputable def ShiftSequenceHom_of_natTrans (F' G' : C ⥤ A) (α : F' ⟶ G') :
    @ShiftSequenceHom _ _ _ _ F' M _ _ G' (Functor.ShiftSequence.tautological F' M)
    (Functor.ShiftSequence.tautological G' M) := by
  refine @ShiftSequenceHom.mk _ _ _ _ F' M _ _ G' (Functor.ShiftSequence.tautological F' M)
    (Functor.ShiftSequence.tautological G' M) (fun n ↦ whiskerLeft (shiftFunctor C n) α) ?_
  intro n a a' h
  ext X
  simp only [ShiftSequence.tautological, comp_obj, whiskerLeft_twice, shiftIso, Iso.trans_hom,
    Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, associator_inv_app,
    whiskerRight_app, assoc, NatTrans.naturality]
  erw [id_comp, id_comp, id_comp, id_comp]

/-- Constructing an `Iso` between the tautological `ShiftSequence`s from a natural isomorphism.
-/
noncomputable def ShiftSequenceIso_of_natIso (F' G' : C ⥤ A) (α : F' ≅ G') :
    @ShiftSequenceIso _ _ _ _ F' M _ _ G' (Functor.ShiftSequence.tautological F' M)
    (Functor.ShiftSequence.tautological G' M) := by
  refine @ShiftSequenceIso.mk _ _ _ _ F' M _ _ G' (Functor.ShiftSequence.tautological F' M)
    (Functor.ShiftSequence.tautological G' M) (fun n ↦ isoWhiskerLeft (shiftFunctor C n) α) ?_
  intro n a a' h
  ext X
  simp only [ShiftSequence.tautological, comp_obj, isoWhiskerLeft_hom, whiskerLeft_twice, shiftIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    associator_inv_app, whiskerRight_app, assoc, NatTrans.naturality]
  erw [id_comp, id_comp, id_comp, id_comp]

end Hom

section Comp

universe u v

variable [F.ShiftSequence M]
variable {D : Type u} [Category.{v,u} D] [HasShift D M] (G : D ⥤ C) [G.CommShift M]

/-- `ShiftSequence` on the composition `G ⋙ F`, where `F` has a `ShiftSequence` and
`G` commutes with shifts.
-/
noncomputable def ShiftSequence.comp_left : ShiftSequence (G ⋙ F) M where
  sequence n := G ⋙ F.shift n
  isoZero := by
    refine NatIso.ofComponents (fun _ ↦ (F.isoShiftZero M).app _) (fun _ ↦ by simp)
  shiftIso n a a' h := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (CommShift.iso n)
    (F.shift a) ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (F.shiftIso n a a' h)
  shiftIso_zero a := by
     ext _
     simp only [comp_obj, CommShift.zero, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
       isoWhiskerLeft_hom, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
       CommShift.isoZero_hom_app, map_comp, associator_hom_app, whiskerLeft_app,
       shiftIso_zero_hom_app, id_obj, id_comp, assoc, comp_map, leftUnitor_hom_app, comp_id]
     rw [← map_comp, Iso.inv_hom_id_app]
     simp
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext _
    simp only [comp_obj, CommShift.add, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
      CommShift.isoAdd_hom_app, map_comp, associator_hom_app, whiskerLeft_app,
      F.shiftIso_add_hom_app n m a a' a'' ha' ha'', id_comp, assoc, whiskerLeft_comp,
      whiskerLeft_twice, comp_map]
    slice_lhs 4 5 => rw [← map_comp, Iso.inv_hom_id_app]; erw [map_id]
    rw [id_comp]
    slice_lhs 3 4 => erw [(F.shiftIso n a a' ha').hom.naturality]
    simp

variable {B : Type*} [Category B] (H : A ⥤ B)

/-- `ShiftSequence` on the composition `F ⋙ H`, where `F` has a `ShiftSequence`.
-/
noncomputable def ShiftSequence.comp_right : ShiftSequence (F ⋙ H) M where
  sequence n := F.shift n ⋙ H
  isoZero := isoWhiskerRight (F.isoShiftZero M) H
  shiftIso n a a' h := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' h) _
  shiftIso_zero a := by aesop
  shiftIso_add n m a a' a'' ha' ha'':= by
    ext _
    simp [F.shiftIso_add_hom_app n m a a' a'' ha' ha'']

end Comp

end Functor

end CategoryTheory
