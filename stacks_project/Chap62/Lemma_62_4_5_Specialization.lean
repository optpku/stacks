module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GenericSpecialMap
public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Induced maps of generic and special fibres

The induced generic- and special-fibre morphisms and their properties are
provided by the shared fibre-map API. Complete types are retained below.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.genericFiberMap : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    X.hom.genericFiber ⟶ Y.hom.genericFiber)

#check (AlgebraicGeometry.Scheme.Hom.genericFiberMap_eq : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    genericFiberMap f =
      fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
        ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
        (genericPoint (Spec (CommRingCat.of R))))

#check (AlgebraicGeometry.Scheme.Hom.genericFiberMap_fiberι : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    genericFiberMap f ≫ Y.hom.genericFiberι = X.hom.genericFiberι ≫ f.left)

#check (AlgebraicGeometry.Scheme.Hom.instIsProper_genericFiberMap :
    ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsProper f.left],
    IsProper (genericFiberMap f))

#check (AlgebraicGeometry.Scheme.Hom.specialFiberMap : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    X.hom.specialFiber ⟶ Y.hom.specialFiber)

#check (AlgebraicGeometry.Scheme.Hom.specialFiberMap_eq : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    specialFiberMap f =
      fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
        ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
        (IsLocalRing.closedPoint R))

#check (AlgebraicGeometry.Scheme.Hom.specialFiberMap_fiberι :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y),
    specialFiberMap f ≫ Y.hom.specialFiberι = X.hom.specialFiberι ≫ f.left)

#check (AlgebraicGeometry.Scheme.Hom.instIsProper_specialFiberMap :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsProper f.left],
    IsProper (specialFiberMap f))

end AlgebraicGeometry.Scheme.Hom
