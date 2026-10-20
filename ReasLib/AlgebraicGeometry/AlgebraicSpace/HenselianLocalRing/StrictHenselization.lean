module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.RingTheory.Henselian.StrictHenselization

/-!
# Étale local rings as strict henselizations of henselian local rings

For a decent algebraic space, elementary étale neighbourhood germs induce a
canonical comparison from the henselian local ring to the étale local ring.
The latter is a strict henselization through this comparison.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- An actual lift of a geometric point through an elementary étale neighbourhood
induces a ring homomorphism from its global sections to the étale stalk. -/
noncomputable def etaleLocalRing.germAlongLift {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (lift : GeometricPoint.OverLift xbar U.obj.toSite) :
    Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤) →+*
      etaleLocalRing X xbar :=
  RingCat.Hom.hom
    ((eqToHom
        ((congrArg (fun Y : Scheme.{u} ↦ RingCat.of Γ(Y, ⊤))
            (EtaleNeighborhood.Elementary.toScheme_obj X xbar.image U).symm).trans
          (structureSheaf_obj U.obj.toSite).symm) :
        RingCat.of Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤) ⟶
          (structureSheaf X).obj.obj (op U.obj.toSite)) ≫
      (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber U.obj.toSite
        lift (structureSheaf X).obj)

/-- A stalk element is an elementary germ of a section when an actual lift sends
the closed point to the selected neighbourhood point and the section to that element. -/
def etaleLocalRing.IsElementaryGerm {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (s : Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤))
    (a : etaleLocalRing X xbar) : Prop :=
  ∃ lift : GeometricPoint.OverLift xbar U.obj.toSite,
    lift.hom.left (IsLocalRing.closedPoint xbar.K) = U.obj.point ∧
      etaleLocalRing.germAlongLift xbar U lift s = a

/-- Select an actually represented elementary germ, returning zero if no such
germ is represented. -/
noncomputable def etaleLocalRing.elementaryGermValue {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (s : Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤)) :
    etaleLocalRing X xbar := by
  classical
  exact if h : ∃ a, etaleLocalRing.IsElementaryGerm xbar U s a then
    Classical.choose h else 0

/-- Every section of an elementary étale neighbourhood has its selected germ
represented by an actual lift through the selected point. -/
theorem etaleLocalRing.elementaryGermValue_spec {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (s : Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤)) :
    etaleLocalRing.IsElementaryGerm xbar U s
      (etaleLocalRing.elementaryGermValue xbar U s) :=
  sorry

/-- Two actual lifts through the selected elementary neighbourhood point give
the same germ of each section. -/
theorem etaleLocalRing.elementaryGermValue_unique {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (s : Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤))
    {a b : etaleLocalRing X xbar}
    (ha : etaleLocalRing.IsElementaryGerm xbar U s a)
    (hb : etaleLocalRing.IsElementaryGerm xbar U s b) : a = b :=
  sorry

/-- Global sections of an elementary étale neighbourhood map canonically to
their germs in the étale local ring. -/
noncomputable def etaleLocalRing.germ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤) →+*
      etaleLocalRing X xbar := by
  let f := etaleLocalRing.elementaryGermValue xbar U
  have laws : f 1 = 1 ∧ (∀ a b, f (a * b) = f a * f b) ∧
      f 0 = 0 ∧ (∀ a b, f (a + b) = f a + f b) := sorry
  exact
    { toFun := f
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- The canonical germ agrees with the stalk coprojection along every actual
lift whose closed point maps to the selected elementary neighbourhood point. -/
theorem etaleLocalRing.germ_eq_of_lift {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image)
    (lift : GeometricPoint.OverLift xbar U.obj.toSite)
    (hpoint : lift.hom.left (IsLocalRing.closedPoint xbar.K) = U.obj.point) :
    etaleLocalRing.germ xbar U = etaleLocalRing.germAlongLift xbar U lift :=
  sorry

/-- Canonical comparison from the henselian local ring at the image of a geometric point
to the étale local ring at that geometric point, induced by germs of elementary étale
neighbourhoods. -/
noncomputable def etaleLocalRing.fromHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    henselianLocalRing X xbar.image →+* etaleLocalRing X xbar :=
  ULift.ringEquiv.toRingHom.comp
    (colimit.desc (EtaleNeighborhood.Elementary.sections X xbar.image)
        { pt :=
            (CommRingCat.universeLift.{u, u + 1}).obj
              (CommRingCat.of (etaleLocalRing X xbar))
          ι :=
            { app := fun j ↦
                (CommRingCat.universeLift.{u, u + 1}).map
                  (CommRingCat.ofHom
                    (etaleLocalRing.germ xbar (ULiftHom.objDown j).unop))
              naturality := fun _ _ _ ↦ sorry } }).hom

/-- The étale local ring is canonically an algebra over the henselian local ring
at the image point through elementary neighbourhood germs. -/
noncomputable instance etaleLocalRing.instAlgebraHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    Algebra (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) :=
  (etaleLocalRing.fromHenselianLocalRing xbar).toAlgebra

/-- The étale local ring at a geometric point is a strict henselization of the
henselian local ring at the image point. -/
instance etaleLocalRing.instIsStrictHenselizationOf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    IsStrictHenselizationOf (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) :=
  sorry

/-- The canonical comparison recovers the germ of global sections of an elementary
étale neighbourhood after composing with the colimit coprojection. -/
theorem etaleLocalRing.fromHenselianLocalRing_comp_ι {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    (etaleLocalRing.fromHenselianLocalRing xbar).comp
        (henselianLocalRing.ι X xbar.image U) =
      etaleLocalRing.germ xbar U :=
  sorry

/-- The structural algebra map from the henselian local ring to the étale local
ring is the canonical comparison induced by germs. -/
theorem etaleLocalRing.algebraMap_fromHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    algebraMap (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) =
      etaleLocalRing.fromHenselianLocalRing xbar :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
