module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisAction
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ResidueGalois
public import Mathlib.CategoryTheory.Action.Continuous
public import ReasLib.CategoryTheory.Action.Continuous
public import Mathlib.FieldTheory.Galois.Profinite

open CategoryTheory Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- The residue field of the image of a geometric point of a field spectrum. -/
abbrev residueFieldOf (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Type u :=
  (Spec (.of K)).residueField s.toFieldValuedPoint.image

/-- The point of a field spectrum defined by the embedded separable closure of its residue field. -/
def geometricPointHom (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Spec (.of s.separableClosure) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap (residueFieldOf K s) s.separableClosure)) ≫
    (Spec (.of K)).fromSpecResidueField s.toFieldValuedPoint.image

/-- The spectrum map of a residue-field Galois automorphism preserves the separable point. -/
theorem geometricPointGaloisIso_hom_comm (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ geometricPointHom K s =
      geometricPointHom K s := sorry

/-- The spectrum map of the inverse Galois automorphism preserves the separable point. -/
theorem geometricPointGaloisIso_inv_comm (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ geometricPointHom K s =
      geometricPointHom K s := sorry

/-- The spectrum maps of a Galois automorphism and its inverse compose to the identity. -/
theorem geometricPointGaloisIso_hom_inv_id (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) =
        𝟙 (Spec (.of s.separableClosure)) := sorry

/-- The spectrum maps of an inverse Galois automorphism and the automorphism compose to the identity. -/
theorem geometricPointGaloisIso_inv_hom_id (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) =
        𝟙 (Spec (.of s.separableClosure)) := sorry

/-- A Galois automorphism induces an automorphism of the separable point over the field spectrum. -/
def geometricPointGaloisIso (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) (σ : s.absoluteGaloisGroup) :
    Over.mk (geometricPointHom K s) ≅ Over.mk (geometricPointHom K s) where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom))
    (geometricPointGaloisIso_hom_comm K s σ)
  inv := Over.homMk (Spec.map (CommRingCat.ofHom σ.symm.toRingHom))
    (geometricPointGaloisIso_inv_comm K s σ)
  hom_inv_id := Over.OverMorphism.ext (geometricPointGaloisIso_hom_inv_id K s σ)
  inv_hom_id := Over.OverMorphism.ext (geometricPointGaloisIso_inv_hom_id K s σ)

/-- The small-étale site point defined by the embedded separable closure of the residue field. -/
def etalePoint (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    ((Spec (.of K)).smallEtaleTopology).Point :=
  Scheme.pointSmallEtale (geometricPointHom K s)

/-- The identity Galois automorphism acts identically on the discrete stalk. -/
theorem stalkGaloisSetAction_one (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    TopCat.discrete.map (TypeCat.ofHom (stalkGaloisAction (geometricPointHom K s)
      (geometricPointGaloisIso K s 1) F.1)) =
        𝟙 (TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1)) := sorry

/-- Multiplication of Galois automorphisms gives composition of their left actions on stalks. -/
theorem stalkGaloisSetAction_mul (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (σ τ : s.absoluteGaloisGroup) :
    TopCat.discrete.map (TypeCat.ofHom (stalkGaloisAction (geometricPointHom K s)
      (geometricPointGaloisIso K s (σ * τ)) F.1)) =
        TopCat.discrete.map (TypeCat.ofHom (stalkGaloisAction (geometricPointHom K s)
          (geometricPointGaloisIso K s τ) F.1)) ≫
        TopCat.discrete.map (TypeCat.ofHom (stalkGaloisAction (geometricPointHom K s)
          (geometricPointGaloisIso K s σ) F.1)) := sorry

/-- The residue-field Galois group acts by precomposition on the discrete separable-point stalk. -/
def stalkGaloisSetAction (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    Action TopCat s.absoluteGaloisGroup where
  V := TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1)
  ρ :=
    { toFun := fun σ ↦ TopCat.discrete.map
        (TypeCat.ofHom
          (stalkGaloisAction (geometricPointHom K s) (geometricPointGaloisIso K s σ) F.1))
      map_one' := stalkGaloisSetAction_one K s F
      map_mul' := stalkGaloisSetAction_mul K s F }

/-- The Galois action on a discrete étale stalk is continuous for the Krull topology. -/
theorem stalkGaloisSetAction_continuous (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    (stalkGaloisSetAction K s F).IsContinuous := sorry

/-- The étale stalk with its discrete topology and continuous residue-field Galois action. -/
def stalkGaloisSetObj (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    DiscreteContAction TopCat s.absoluteGaloisGroup :=
  ⟨⟨stalkGaloisSetAction K s F, stalkGaloisSetAction_continuous K s F⟩,
    inferInstanceAs
      (DiscreteTopology (TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1)))⟩

/-- A morphism of étale sheaves induces a Galois-equivariant map of discrete stalks. -/
theorem stalkGaloisSetMap_comm (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (σ : s.absoluteGaloisGroup) :
    (stalkGaloisSetAction K s F).ρ σ ≫
      TopCat.discrete.map ((etalePoint K s).presheafFiber.map f.1) =
        TopCat.discrete.map ((etalePoint K s).presheafFiber.map f.1) ≫
          (stalkGaloisSetAction K s G).ρ σ := sorry

/-- The morphism of discrete continuous Galois sets induced by a morphism of étale sheaves. -/
def stalkGaloisSetMap (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G) :
    stalkGaloisSetObj K s F ⟶ stalkGaloisSetObj K s G :=
  ObjectProperty.homMk <| ObjectProperty.homMk
    { hom := TopCat.discrete.map ((etalePoint K s).presheafFiber.map f.1)
      comm := stalkGaloisSetMap_comm K s f }

/-- The stalk map of the identity sheaf morphism is the identity Galois-set morphism. -/
theorem stalkGaloisSetMap_id (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    stalkGaloisSetMap K s (𝟙 F) = 𝟙 (stalkGaloisSetObj K s F) := sorry

/-- Taking stalk maps preserves composition of sheaf morphisms. -/
theorem stalkGaloisSetMap_comp (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    {F G H : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)}
    (f : F ⟶ G) (g : G ⟶ H) :
    stalkGaloisSetMap K s (f ≫ g) = stalkGaloisSetMap K s f ≫ stalkGaloisSetMap K s g := sorry

/-- Taking étale stalks defines a functor to discrete continuous residue-field Galois sets. -/
def stalkGaloisSet (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))) :
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ⥤
      DiscreteContAction TopCat s.absoluteGaloisGroup where
  obj := stalkGaloisSetObj K s
  map := stalkGaloisSetMap K s
  map_id := stalkGaloisSetMap_id K s
  map_comp := stalkGaloisSetMap_comp K s

/-- The underlying discrete space of the stalk functor is the separable-point presheaf fiber. -/
theorem stalkGaloisSet_obj_carrier (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    ((stalkGaloisSet K s).obj F).obj.obj.V =
      TopCat.discrete.obj ((etalePoint K s).presheafFiber.obj F.1) := rfl

/-- The bundled stalk action evaluates as precomposition by the geometric-point automorphism. -/
theorem stalkGaloisSet_smul_apply (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (σ : s.absoluteGaloisGroup) (x : (etalePoint K s).presheafFiber.obj F.1) :
    ConcreteCategory.hom (((stalkGaloisSet K s).obj F).obj.obj.ρ σ) x =
      stalkGaloisAction (geometricPointHom K s) (geometricPointGaloisIso K s σ) F.1 x := rfl

/-- The bundled map on stalks evaluates as the map of presheaf fibers. -/
theorem stalkGaloisSet_map_apply (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)} (f : F ⟶ G)
    (x : (etalePoint K s).presheafFiber.obj F.1) :
    ConcreteCategory.hom (((stalkGaloisSet K s).map f).hom.hom.hom) x =
      (etalePoint K s).presheafFiber.map f.1 x := rfl

/-- The inclusion of the embedded separable closure factors the original geometric-point morphism. -/
theorem geometricPointInclusion_comp (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    Spec.map (CommRingCat.ofHom s.separableClosure.val.toRingHom) ≫
      geometricPointHom K s = s.hom := sorry

/-- The natural map from the separable-point stalk to the original geometric-point stalk,
induced by the inclusion of the separable closure into the algebraically closed source field. -/
def separableStalkToGeometricStalk (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    (etalePoint K s).sheafFiber (A := Type u) ⟶
      (@Scheme.pointSmallEtale _ s.K s.field
        (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (⟨Functor.whiskerLeft (Etale.forget (Spec (.of K)))
      (coyoneda.map (Over.homMk
        (Spec.map (CommRingCat.ofHom s.separableClosure.val.toRingHom))
        (geometricPointInclusion_comp K s)).op)⟩ :
      @Scheme.pointSmallEtale _ s.K s.field
        (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom ⟶ etalePoint K s)

/-- The stalk comparison sends a germ to the germ whose lift is composed with the field inclusion. -/
theorem separableStalkToGeometricStalk_on_generator (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u))
    (U : (Spec (.of K)).Etale) (lift : (etalePoint K s).fiber.obj U)
    (sectionValue : F.1.obj (op U)) :
    (separableStalkToGeometricStalk K s).app F
      ((etalePoint K s).toPresheafFiber U lift F.1 sectionValue) =
        (@Scheme.pointSmallEtale _ s.K s.field
          (@IsSepClosed.of_isAlgClosed s.K s.field s.isAlgClosed) s.hom).toPresheafFiber U
          (Over.homMk (U := Over.mk s.hom) (V := Over.mk (geometricPointHom K s))
            (Spec.map (CommRingCat.ofHom s.separableClosure.val.toRingHom))
            (geometricPointInclusion_comp K s) ≫ lift) F.1 sectionValue := sorry

/-- Every component of the comparison between separable and geometric stalks is bijective. -/
theorem separableStalkToGeometricStalk_bijective (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    Function.Bijective ((separableStalkToGeometricStalk K s).app F) := sorry

/-- Taking the étale stalk at any geometric point of a field spectrum is an equivalence
between sheaves of sets and discrete continuous residue-field Galois sets. -/
theorem stalkGaloisSet_isEquivalence (K : Type u) [Field K]
    (s : GeometricPoint (Spec (.of K))) :
    (stalkGaloisSet K s).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Etale
