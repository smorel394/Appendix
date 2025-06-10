import Mathlib.CategoryTheory.Shift.CommShift

open CategoryTheory Category Functor CommShift

namespace CategoryTheory

namespace Functor

section hasShiftOfFullyFaithful

variable {C D : Type _} [Category C] [Category D]
  {A : Type _} [AddMonoid A] [HasShift D A]
  {F : C ⥤ D} (hF : F.FullyFaithful)
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

def of_hasShiftOfFullyFaithful :
    letI := hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { iso := i
    zero := by
      ext X
      simp only [comp_obj, isoZero_hom_app, ShiftMkCore.shiftFunctorZero_eq, Iso.symm_hom,
        FullyFaithful.hasShift.map_zero_hom_app, id_obj, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id]
    add := fun a b => by
      ext X
      simp only [comp_obj, isoAdd_hom_app, ShiftMkCore.shiftFunctorAdd_eq, Iso.symm_hom,
        FullyFaithful.hasShift.map_add_hom_app, Category.assoc, ShiftMkCore.shiftFunctor_eq,
        Iso.inv_hom_id_app_assoc, ← (shiftFunctor D b).map_comp_assoc, Iso.inv_hom_id_app,
        Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] }

end CommShift

lemma shiftFunctorIso_of_hasShiftOfFullyFaithful (a : A) :
    letI := hF.hasShift s i;
    letI := CommShift.of_hasShiftOfFullyFaithful hF s i;
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

end Functor

end CategoryTheory
