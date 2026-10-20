/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension of complexes and change of coefficients

Extension by zero along an embedding of complex shapes commutes canonically with every functor
preserving zero morphisms.  The comparison is constructed degreewise: on the image of the
embedding it is the evident identity comparison, and off the image it is the unique isomorphism
between zero objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vA vB uA uB

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B]
variable [HasZeroMorphisms A] [HasZeroMorphisms B]
variable [HasZeroObject A] [HasZeroObject B]
variable (e : c.Embedding c') (F : A ⥤ B) [F.PreservesZeroMorphisms]

/-- Extend an `A`-valued complex by zero and then apply `F` termwise. -/
abbrev mapSource :
    HomologicalComplex A c ⥤ HomologicalComplex B c' :=
  e.extendFunctor A ⋙ F.mapHomologicalComplex c'

/-- Apply `F` termwise and then extend the resulting `B`-valued complex by zero. -/
abbrev mapTarget :
    HomologicalComplex A c ⥤ HomologicalComplex B c' :=
  F.mapHomologicalComplex c ⋙ e.extendFunctor B

/-- The degreewise comparison between applying `F` after extension and extending after applying
`F`.  On degrees in the image of `e` it uses `extendXIso`; elsewhere it is the unique
isomorphism between zero objects. -/
noncomputable def mapComponentIso (K : HomologicalComplex A c) (i' : ι') :
    ((mapSource e F).obj K).X i' ≅ ((mapTarget e F).obj K).X i' :=
  open scoped Classical in
    if h : ∃ i, e.f i = i' then
      F.mapIso (K.extendXIso e h.choose_spec) ≪≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
    else
      (F.map_isZero
        (K.isZero_extend_X e i' (fun i hi ↦ h ⟨i, hi⟩))).iso
          (((F.mapHomologicalComplex c).obj K).isZero_extend_X
            e i' (fun i hi ↦ h ⟨i, hi⟩))

/-- On a degree explicitly identified with `e.f i`, `mapComponentIso` is the canonical
comparison through the two `extendXIso` maps. -/
theorem mapComponentIso_of_eq (K : HomologicalComplex A c)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    mapComponentIso e F K i' =
      F.mapIso (K.extendXIso e h) ≪≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).symm := sorry

/-- Off the image of `e`, `mapComponentIso` is the unique isomorphism between the two zero
objects. -/
theorem mapComponentIso_of_not_mem (K : HomologicalComplex A c) (i' : ι')
    (h : ∀ i, e.f i ≠ i') :
    mapComponentIso e F K i' =
      (F.map_isZero (K.isZero_extend_X e i' h)).iso
        (((F.mapHomologicalComplex c).obj K).isZero_extend_X e i' h) := sorry

/-- The degreewise extension comparisons commute with differentials. -/
theorem mapComponentIso_comm (K : HomologicalComplex A c) (i' j' : ι')
    (h : c'.Rel i' j') :
    (mapComponentIso e F K i').hom ≫ ((mapTarget e F).obj K).d i' j' =
      ((mapSource e F).obj K).d i' j' ≫ (mapComponentIso e F K j').hom := sorry

/-- Change of coefficients commutes with extension by zero on one complex. -/
noncomputable def mapAppIso (K : HomologicalComplex A c) :
    (mapSource e F).obj K ≅ (mapTarget e F).obj K :=
  HomologicalComplex.Hom.isoOfComponents (mapComponentIso e F K)
    (mapComponentIso_comm e F K)

/-- The extension-by-zero comparison is natural in the complex. -/
theorem mapAppIso_hom_naturality {K L : HomologicalComplex A c} (f : K ⟶ L) :
    (mapSource e F).map f ≫ (mapAppIso e F L).hom =
      (mapAppIso e F K).hom ≫ (mapTarget e F).map f := sorry

/-- Extension by zero along a shape embedding commutes canonically with every
zero-morphism-preserving change of coefficients. -/
@[stacks 01EQ "extension by zero commutes with change of coefficients"]
noncomputable def mapFunctorIso : mapSource e F ≅ mapTarget e F :=
  NatIso.ofComponents (mapAppIso e F)
    (fun f ↦ mapAppIso_hom_naturality e F f)

end ComplexShape.Embedding
