/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.Category.TopCat.OpenNhds

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open TopologicalSpace

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

namespace Etale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The stalk ring of the small étale structure sheaf at a separably closed field-valued point. -/
noncomputable abbrev stalkRing (point : Spec (.of Ω) ⟶ S) : Type u :=
  ((@pointSmallEtale S Ω inferInstance inferInstance point).presheafFiber :
      (S.Etaleᵒᵖ ⥤ RingCat) ⥤ RingCat).obj
    ((Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)

/-- Multiplication in the étale stalk ring is commutative. -/
theorem stalkRing.mul_comm (point : Spec (.of Ω) ⟶ S)
    (first second : stalkRing point) : first * second = second * first := sorry

/-- The étale stalk ring has its canonical commutative-ring structure. -/
instance stalkRing.commRing (point : Spec (.of Ω) ⟶ S) : CommRing (stalkRing point) :=
  { (inferInstance : Ring (stalkRing point)) with
    mul_comm := stalkRing.mul_comm point }

end Etale

/-- The étale local ring of a scheme at a geometric point is its small-étale stalk ring. -/
noncomputable abbrev etaleLocalRing (S : Scheme.{u}) (s : GeometricPoint S) : Type u :=
  @Etale.stalkRing S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

/-- The étale local ring is definitionally the fiber of the small-étale structure sheaf. -/
theorem etaleLocalRing_def (S : Scheme.{u}) (s : GeometricPoint S) :
    etaleLocalRing S s =
      ((@pointSmallEtale S s.K inferInstance
          (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber :
          (S.Etaleᵒᵖ ⥤ RingCat) ⥤ RingCat).obj
        ((Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat) := sorry

/-- The geometric-point commutativity statement is inherited from the raw stalk ring. -/
abbrev etaleLocalRing.mul_comm (S : Scheme.{u}) (s : GeometricPoint S)
    (first second : etaleLocalRing S s) : first * second = second * first :=
  @Etale.stalkRing.mul_comm S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom first second

/-- The geometric-point étale local ring with its canonical commutative-ring structure. -/
abbrev etaleLocalRing.commRing (S : Scheme.{u}) (s : GeometricPoint S) :
    CommRing (etaleLocalRing S s) :=
  @Etale.stalkRing.commRing S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

/-- Sections of the small-étale structure sheaf are commutative rings. -/
instance etaleLocalRing.structureSheafObjCommRing (S : Scheme.{u}) (V : S.Etale) :
    CommRing (((Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙
      forget₂ CommRingCat RingCat).obj (op V)) :=
  { (inferInstance : Ring (((Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙
        forget₂ CommRingCat RingCat).obj (op V))) with
    mul_comm := sorry }

namespace Etale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Canonical comparison from the Zariski stalk to a raw étale stalk ring. -/
noncomputable def stalkRing.fromZariskiStalk
    (point : Spec (.of Ω) ⟶ S) :
    S.presheaf.stalk (point default) →+* Etale.stalkRing point :=
  CommRingCat.Hom.hom <|
    colimit.desc ((OpenNhds.inclusion (X := (S : TopCat)) (point default)).op ⋙ S.presheaf)
      { pt := @CommRingCat.of _ (Etale.stalkRing.commRing point)
        ι := {
          app := fun U =>
            let V : S.Opens := U.unop.1
            let X : S.Etale := Scheme.Etale.mk (Scheme.Opens.ι V)
            let range_subset : Set.range point ⊆ Set.range (Scheme.Opens.ι V) := by
              rintro _ ⟨point, rfl⟩
              rw [Subsingleton.elim point default]
              exact ⟨⟨_, U.unop.2⟩, rfl⟩
            let lift := IsOpenImmersion.lift (Scheme.Opens.ι V) point range_subset
            let fiberPoint : (@pointSmallEtale S Ω inferInstance inferInstance point).fiber.obj X :=
              Over.homMk lift (by
                exact IsOpenImmersion.lift_fac (Scheme.Opens.ι V) point range_subset)
            (eqToHom (by rfl) ≫
              CommRingCat.ofHom (CommRingCat.Hom.hom V.topIso.inv)) ≫
              @CommRingCat.ofHom _ _ inferInstance (Etale.stalkRing.commRing point)
                (RingCat.Hom.hom
                  ((@pointSmallEtale S Ω inferInstance inferInstance point).toPresheafFiber X fiberPoint
                    ((Scheme.smallEtaleToScheme S).op ⋙ Scheme.Γ ⋙
                      forget₂ CommRingCat RingCat)))
          naturality := fun _ _ _ => sorry } }

/-- The étale stalk ring is an algebra over the Zariski stalk at the image of its point. -/
instance stalkRing.algebra (point : Spec (.of Ω) ⟶ S) :
    Algebra (S.presheaf.stalk (point default)) (Etale.stalkRing point) :=
  @RingHom.toAlgebra (S.presheaf.stalk (point default)) (Etale.stalkRing point)
    inferInstance (CommRing.toCommSemiring (s := Etale.stalkRing.commRing point))
    (Etale.stalkRing.fromZariskiStalk point)

/-- A raw étale stalk ring is a strict henselization of the Zariski stalk at its point. -/
instance stalkRing.isStrictHenselizationOf (point : Spec (.of Ω) ⟶ S) :
    IsStrictHenselizationOf (S.presheaf.stalk (point default)) (Etale.stalkRing point) := sorry

end Etale

/-- The étale local ring is an algebra over the Zariski local ring at the image point. -/
abbrev etaleLocalRing.algebra
    (S : Scheme.{u}) (s : GeometricPoint S) :
    Algebra (S.presheaf.stalk s.image) (etaleLocalRing S s) :=
  @Etale.stalkRing.algebra S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

/-- The étale local ring as a bundled commutative ring, with its original stalk carrier
and ring operations. -/
noncomputable def etaleLocalRing.asCommRing (S : Scheme.{u}) (s : GeometricPoint S) :
    CommRingCat :=
  @CommRingCat.of (etaleLocalRing S s) (etaleLocalRing.commRing S s)

/-- The étale local ring as a bundled algebra over the Zariski local ring, with the
algebra structure induced by the comparison on germs. -/
noncomputable def etaleLocalRing.asAlgebra (S : Scheme.{u}) (s : GeometricPoint S) :
    CommAlgCat (S.presheaf.stalk s.image) :=
  @CommAlgCat.of (S.presheaf.stalk s.image) inferInstance (etaleLocalRing S s)
      (etaleLocalRing.commRing S s) (etaleLocalRing.algebra S s)

/-- Canonical comparison from the Zariski stalk to the étale local ring at a geometric point. -/
abbrev etaleLocalRing.fromZariskiStalk
    (S : Scheme.{u}) (s : GeometricPoint S) :
    S.presheaf.stalk s.image →+* etaleLocalRing S s :=
  @Etale.stalkRing.fromZariskiStalk S s.K inferInstance
    (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom

/-- The comparison `fromZariskiStalk` is the algebra map of the bundled étale local ring. -/
theorem etaleLocalRing.fromZariskiStalk_algebraMap
    (S : Scheme.{u}) (s : GeometricPoint S) :
    algebraMap (S.presheaf.stalk s.image) (etaleLocalRing.asAlgebra S s) =
      etaleLocalRing.fromZariskiStalk S s := sorry

/-- The étale local ring at a geometric point is a strict henselization of the
Zariski local ring at the image point, relative to that geometric point. -/
theorem etaleLocalRing.isStrictHenselizationOf
    (S : Scheme.{u}) (s : GeometricPoint S) :
    IsStrictHenselizationOf (S.presheaf.stalk s.image)
      (etaleLocalRing.asAlgebra S s) := by
  simpa [etaleLocalRing.asAlgebra] using
    (@Etale.stalkRing.isStrictHenselizationOf S s.K inferInstance
      (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom)

end AlgebraicGeometry.Scheme
