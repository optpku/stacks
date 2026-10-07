module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.«88_27_0_1_IsoOverOpen»
public import stacks_project.Chap88.«88_27_0_1_RigEtale»

/-!
# Completion functor along a closed subset

The functor sending a morphism of algebraic spaces that is locally of finite
type and an isomorphism over the open complement of `T` to the induced morphism
of completions, landing in rig-étale morphisms of locally Noetherian formal
algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The open complement of a closed subset of the points of an algebraic space. -/
def openComplement {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    Opens (Points X) :=
  ⟨(T : Set (Points X))ᶜ, T.isClosed.isOpen_compl⟩

/-- The open algebraic space `U ⊂ X` with `|U| = |X| \ T`. -/
def openComplementAlong {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    AlgebraicSpace S :=
  OpenSubspace.ofOpensSpace (openComplement X T)

/-- The open immersion of the complement of `T` into `X`. -/
def openComplementι {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    openComplementAlong X T ⟶ X :=
  OpenSubspace.ofOpensι (openComplement X T)

/-- The inclusion of the open complement of `T` is an open immersion. -/
instance instIsOpenImmersion_openComplementι {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) : IsOpenImmersion (openComplementι X T) :=
  OpenSubspace.instIsOpenImmersion_ofOpensι (openComplement X T)

/-- The functor of points of `openComplementAlong X T` is the subfunctor of maps
into the complement of `T`. -/
theorem openComplementAlong_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    (openComplementAlong X T).functorOfPoints =
      (OpenSubspace.ofOpensSubfunctor (openComplement X T)).toFunctor :=
  sorry

/-- The image of `|openComplementAlong X T|` in `|X|` is the complement of `T`. -/
theorem openComplementAlong_pointsSet {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Closeds (Points X)) :
    Set.range (Points.map (openComplementι X T)) = (T : Set (Points X))ᶜ :=
  sorry

namespace completionAlong

/-- The source category `C_{X,T}` of morphisms `f : X' ⟶ X` that are locally of
finite type and isomorphisms over the open complement of `T`. -/
abbrev Source {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :=
  LocallyOfFiniteTypeIsoOverOpen (openComplementι X T)

/-- The target category of morphisms `g : W ⟶ X_/T` of formal algebraic spaces
with `W` locally Noetherian and `g` rig-étale. -/
abbrev Target {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :=
  FormalAlgebraicSpace.LocallyNoetherianRigEtaleOver (completionAlong X T)

/-- The completion of a locally Noetherian algebraic space along a closed subset
is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

/-- The completion of a locally Noetherian algebraic space along a closed subset
is a locally Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T) :=
  sorry

/-- Completing the source of a locally finite-type morphism into a locally
Noetherian algebraic space yields a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_preimage {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (f : X' ⟶ X) (T : Closeds (Points X))
    [LocallyOfFiniteType f] :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- Completing the source of a locally finite-type morphism into a locally
Noetherian algebraic space yields a locally Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_preimage {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (f : X' ⟶ X) (T : Closeds (Points X))
    [LocallyOfFiniteType f] :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- Completing a locally-of-finite-type morphism that is an isomorphism over the
open complement of `T` yields a rig-étale morphism of formal algebraic spaces. -/
instance instRigEtale_map {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (f : X' ⟶ X) (T : Closeds (Points X))
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))] :
    FormalAlgebraicSpace.RigEtale (map f T) :=
  sorry

/-- The morphism of completions over `X` induced by a morphism in `Over X`. -/
def mapOver {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    completionAlong Y.left (T.preimage (Points.continuous_map Y.hom)) ⟶
      completionAlong Y'.left (T.preimage (Points.continuous_map Y'.hom)) where
  app U := ofHom fun x ↦ ⟨φ.left.app U x.1, sorry⟩
  naturality := sorry

/-- Postcomposing `mapOver T φ` with `completionAlong.map Y'.hom T` recovers
`completionAlong.map Y.hom T`. -/
theorem mapOver_comp_map {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    mapOver T φ ≫ map Y'.hom T = map Y.hom T :=
  sorry

/-- The object of `Target X T` obtained by completing a source morphism along
`T`. -/
def functorObj {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (Y : Source X T) : Target X T where
  obj := Over.mk (map Y.obj.hom T)
  property := sorry

/-- The morphism of `Target X T` obtained by completing a morphism of source
objects along `T`. -/
def functorMap {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    functorObj T Y ⟶ functorObj T Y' :=
  ObjectProperty.homMk (Over.homMk (mapOver T φ.hom) (mapOver_comp_map T φ.hom))

/-- Completing identity morphisms in `Source X T` yields identity morphisms. -/
theorem functorMap_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (Y : Source X T) :
    functorMap T (𝟙 Y) = 𝟙 (functorObj T Y) :=
  sorry

/-- Completing composites in `Source X T` yields composites. -/
theorem functorMap_comp {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' Y'' : Source X T} (φ : Y ⟶ Y') (ψ : Y' ⟶ Y'') :
    functorMap T (φ ≫ ψ) = functorMap T φ ≫ functorMap T ψ :=
  sorry

/-- The completion functor sending `f : X' ⟶ X` to `f_/T : X'_/T' ⟶ X_/T`. -/
def functor {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) : Source X T ⥤ Target X T where
  obj := functorObj T
  map := functorMap T
  map_id := functorMap_id T
  map_comp := functorMap_comp T

/-- The object map of `functor X T` is completion of the structure morphism along
`T`. -/
theorem functor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (Y : Source X T) :
    ((functor X T).obj Y).obj.hom = map Y.obj.hom T :=
  sorry

/-- The morphism map of `functor X T` is `mapOver` of the underlying arrow. -/
theorem functor_map {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    (((functor X T).map φ).hom).left = mapOver T φ.hom :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
