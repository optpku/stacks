/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Adjunction.Whiskering

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- The connecting value of a global section in a short exact sequence of scheme modules,
obtained by composing its degree-zero Ext class with the extension class of the underlying
short exact sequence of additive sheaves. -/
noncomputable def cohomologyBoundaryFromExt
    (f : X ⟶ Spec (.of A)) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (globalSection : globalSectionsMod f S.X₃) : cohomology f S.X₁ 1 :=
  let topology := Opens.grothendieckTopology X.carrier
  let generators := (yoneda.obj (⊤ : Opens X)) ⋙ AddCommGrpCat.free
  let sectionHom :=
    (((sheafificationAdjunction topology AddCommGrpCat).homEquiv generators
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃)).trans
      (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv
          (yoneda.obj (⊤ : Opens X))
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj).trans yonedaEquiv)).symm
      globalSection
  let zeroPreserving :
      (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  let mappedShortExact :
      (@CategoryTheory.ShortComplex.map _ _ _ _ _ _ S
        (SheafOfModules.toSheaf X.ringCatSheaf) zeroPreserving).ShortExact :=
    @CategoryTheory.ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hS
      (SheafOfModules.toSheaf X.ringCatSheaf) zeroPreserving
      (SheafOfModules.toSheaf_exact X.ringCatSheaf).1
      (SheafOfModules.toSheaf_exact X.ringCatSheaf).2
  (eqToHom (cohomologyForget_obj_eq f S.X₁ 1).symm)
    ((Abelian.Ext.mk₀ sectionHom).comp
      mappedShortExact.extClass (zero_add 1))

end AlgebraicGeometry.Scheme.Hom
