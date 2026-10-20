module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Support properties of abelian sheaves on algebraic spaces

Local section supports are closed and satisfy inclusions under addition and sheaf maps.
Sheaf support is the union of images of local section supports and is monotone under
monomorphisms and antitone under epimorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The support of a local section of an abelian sheaf is closed in its domain. -/
theorem isClosed_abelianSheafSectionSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    IsClosed (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  (abelianSheafSectionSupport F U σ).isClosed

/-- The support of a sum of two sections over the same étale object is contained in the
union of their supports. -/
theorem abelianSheafSectionSupport_add_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ σ' : F.obj.obj (op U)) :
    (abelianSheafSectionSupport F U (σ + σ') : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left) ∪
        (abelianSheafSectionSupport F U σ' : Set U.left.left) :=
  sorry

/-- The image of a local section under a morphism of abelian sheaves has support contained
in the support of the original section. -/
theorem abelianSheafSectionSupport_map_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)) :
    (abelianSheafSectionSupport G U (φ.hom.app (op U) σ) : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  sorry

/-- The support of an abelian sheaf is the union of the images of the supports of all its
local sections. -/
theorem abelianSheafSupport_eq_iUnion_sectionSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    abelianSheafSupport F =
      ⋃ (U : smallEtaleSite X) (σ : F.obj.obj (op U)),
        Points.mapOfOver U.hom '' (abelianSheafSectionSupport F U σ : Set U.left.left) :=
  sorry

/-- The support of the target of an epimorphism of abelian sheaves is contained in the
support of its source. -/
theorem abelianSheafSupport_subset_of_epi {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    abelianSheafSupport G ⊆ abelianSheafSupport F :=
  sorry

/-- The support of the source of a monomorphism of abelian sheaves is contained in the
support of its target. -/
theorem abelianSheafSupport_subset_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Mono φ] :
    abelianSheafSupport F ⊆ abelianSheafSupport G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

end
