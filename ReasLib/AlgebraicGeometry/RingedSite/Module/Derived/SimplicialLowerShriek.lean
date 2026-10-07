module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek.Triangulated
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek on a simplicial site

This file owns the reusable simplicial specialization of the projection lower-shriek.  The
underlying additive-sheaf functor and the derived inverse image are imported canonical owners;
the chapter only needs the short `lowerShriek` name.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSite.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasSheafify (SimplicialSite.topology J) AddCommGrpCat.{w}]
variable [GrothendieckTopology.WEqualsLocallyBijective
  (SimplicialSite.topology J) AddCommGrpCat.{w}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [Functor.IsRightAdjoint
  (siteAbelianInverseImageDerived (SimplicialSite.topology J) J
    SimplicialSite.projection)]

/-- The derived lower shriek along the simplicial-site projection. -/
@[stacks 09D2 "simplicial projection derived lower shriek"]
noncomputable abbrev lowerShriek
    (A : SimplicialObject (Sheaf J CommRingCat.{w})) :
    DerivedCategory (SimplicialSite.ModuleCat.{u, v, w, w}
      (C := C) (J := J) A) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{w}) :=
  RingedSite.Hom.underlyingAbelianSheafDerived
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf A)) ⋙
    Functor.leftAdjoint
      (siteAbelianInverseImageDerived (SimplicialSite.topology J) J
        SimplicialSite.projection)

/-- Derived extension of scalars along a map of simplicial structure sheaves. -/
@[stacks 09D2 "simplicial derived change of rings"]
noncomputable abbrev tensor
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) :
    DerivedCategory (SimplicialSite.ModuleCat.{u, v, w, w}
      (C := C) (J := J) A) ⥤
      DerivedCategory (SimplicialSite.ModuleCat.{u, v, w, w}
        (C := C) (J := J) B) :=
  SheafOfModules.RingedSite.SameSite.pullbackDerived.{u, v, w}
    (SimplicialSite.ringSheafMap α)

/-- The source-facing change-of-rings functor exposes the canonical shift owner of its
underlying same-site derived pullback, so compositions can use the standard `CommShift.comp`
instance without a local typeclass pin. -/
@[stacks 09D2 "simplicial derived change-of-rings shift"]
noncomputable instance tensor.commShift
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) :
    (tensor α).CommShift ℤ :=
  RingedSite.Hom.modulePullbackDerived.commShift
    (f := SheafOfModules.RingedSite.sameSiteHom (SimplicialSite.ringSheafMap α))

/-- The unit comparison used by the source projection formula, in its canonical free-module
presentation.  Its target is the image under `lowerShriek A` of the identity-site
pushforward/restriction of the free unit for `B`; this is the source-facing comparison used by
the change-of-rings theorem, rather than a separately chosen map to `lowerShriek B` applied to a
unit object. -/
@[stacks 09D2 "simplicial projection unit comparison"]
noncomputable abbrev unitComparison
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) :=
  (lowerShriek A).map
    ((DerivedCategory.singleFunctor
      (SimplicialSite.ModuleCat.{u, v, w, w} (C := C) (J := J) A)
      (0 : ℤ)).map
      (SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.RingedSite.ringedSiteStructureMap
          (SimplicialSite.ringSheafMap α))))

/-- The unit comparison as an isomorphism once its canonical invertibility certificate is
available.  This keeps downstream constructions on the named comparison rather than on an
unspecified existential isomorphism. -/
@[stacks 09D2 "simplicial projection unit comparison isomorphism"]
noncomputable abbrev unitComparisonIso
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) [IsIso (unitComparison α)] :=
  asIso (unitComparison α)

/-- Lemma 21.41.2: an invertible unit comparison identifies projection lower shriek after
derived extension of scalars. -/
@[stacks 09D2 "projection lower-shriek change-of-rings comparison"]
theorem tensor.lowerShriek_isomorphic
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) [IsIso (unitComparison α)] :
    IsIsomorphic (lowerShriek A) (tensor α ⋙ lowerShriek B) := sorry

/-- The functor comparison has the corresponding objectwise form. -/
@[stacks 09D2 "objectwise projection lower-shriek comparison"]
theorem tensor.lowerShriek_obj_isomorphic
    {A B : SimplicialObject (Sheaf J CommRingCat.{w})}
    (α : A ⟶ B) [IsIso (unitComparison α)]
    (K : DerivedCategory
      (SimplicialSite.ModuleCat.{u, v, w, w} (C := C) (J := J) A)) :
    IsIsomorphic ((lowerShriek A).obj K) ((tensor α ⋙ lowerShriek B).obj K) := sorry

/-- The simplicial projection lower shriek admits a triangulated-functor structure.  The
proposition form deliberately leaves the noncanonical shift comparison to the downstream use
site. -/
@[stacks 09D3 "simplicial projection lower shriek triangulated structure"]
theorem lowerShriek.hasTriangulatedStructure
    (A : SimplicialObject (Sheaf J CommRingCat.{w})) :
    (lowerShriek A).HasTriangulatedStructure := sorry

/- The repeated lower-shriek expression is available under a scoped source-facing notation. -/
set_option quotPrecheck false in
scoped[SimplicialSite] notation:max "Lπ![" A:max "]" =>
  _root_.CategoryTheory.SimplicialSite.Derived.lowerShriek A

end CategoryTheory.SimplicialSite.Derived
