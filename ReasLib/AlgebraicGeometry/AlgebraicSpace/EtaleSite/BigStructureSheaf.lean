module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big

/-!
# Structure sheaf on the big étale site of an algebraic space

The sheaf `𝒪` on `(Spaces/X)_étale` is `U ↦ Γ(U, 𝒪_U)`, obtained by evaluating the
spaces-étale structure sheaf of `U` at the terminal object `U/U`. Restriction is the
map on global sections induced by a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

variable {S : Scheme.{u}}

/-- Global sections `Γ(Z, 𝒪_Z)` as the value of the spaces-étale structure sheaf of `Z`
at the terminal object `Z/Z`. -/
def gamma (Z : AlgebraicSpace S) : RingCat.{u} :=
  (spacesStructureSheaf Z).obj.obj (op (spacesEtaleSite.self Z))

/-- `gamma Z` is the spaces-étale structure sheaf of `Z` evaluated at `spacesEtaleSite.self Z`. -/
theorem gamma_eq (Z : AlgebraicSpace S) :
    gamma Z = (spacesStructureSheaf Z).obj.obj (op (spacesEtaleSite.self Z)) :=
  rfl

/-- Base change of the terminal object of `X_spaces,étale` along `f : Y ⟶ X` is canonically
isomorphic to the terminal object of `Y_spaces,étale`. -/
def pullbackSelfIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (spacesEtalePullback f).obj (spacesEtaleSite.self X) ≅ spacesEtaleSite.self Y :=
  ((isTerminal_self X).isTerminalObj (spacesEtalePullback f)).uniqueUpToIso (isTerminal_self Y)

/-- `pullbackSelfIso f` identifies the base-changed terminal object with `Y/Y`. -/
theorem pullbackSelfIso_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    pullbackSelfIso f =
      ((isTerminal_self X).isTerminalObj (spacesEtalePullback f)).uniqueUpToIso
        (isTerminal_self Y) :=
  rfl

/-- Restriction `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` along a morphism of algebraic spaces, obtained from
`spacesStructureSheafMap` by evaluating at the terminal object and transporting along
`pullbackSelfIso`. -/
def gammaMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) : gamma X ⟶ gamma Y :=
  (spacesStructureSheafMap f).hom.app (op (spacesEtaleSite.self X)) ≫
    (spacesStructureSheaf Y).obj.map (op (pullbackSelfIso f).inv)

/-- `gammaMap f` is `spacesStructureSheafMap f` at `X/X`, transported along `pullbackSelfIso f`. -/
theorem gammaMap_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    gammaMap f =
      (spacesStructureSheafMap f).hom.app (op (spacesEtaleSite.self X)) ≫
        (spacesStructureSheaf Y).obj.map (op (pullbackSelfIso f).inv) :=
  rfl

/-- Pullback of global sections along an identity is the identity. -/
theorem gammaMap_id (X : AlgebraicSpace S) : gammaMap (𝟙 X) = 𝟙 (gamma X) :=
  sorry

/-- Pullback of global sections reverses composition. -/
theorem gammaMap_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    gammaMap (f ≫ g) = gammaMap g ≫ gammaMap f :=
  sorry

/-- The contravariant global-sections functor `Z ↦ Γ(Z, 𝒪_Z)` on algebraic spaces over `S`. -/
def gammaFunctor : (AlgebraicSpace S)ᵒᵖ ⥤ RingCat.{u} where
  obj Z := gamma Z.unop
  map g := gammaMap g.unop
  map_id Z := gammaMap_id Z.unop
  map_comp f g := gammaMap_comp g.unop f.unop

/-- `gammaFunctor` evaluates to `gamma` on objects. -/
theorem gammaFunctor_obj (Z : AlgebraicSpace S) : gammaFunctor.obj (op Z) = gamma Z :=
  rfl

/-- `gammaFunctor` acts on morphisms by `gammaMap`. -/
theorem gammaFunctor_map {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    gammaFunctor.map f.op = gammaMap f :=
  rfl

/-- The structure presheaf on `(Spaces/X)_étale`, sending `U` to `Γ(U, 𝒪_U)`. -/
def structurePresheaf (X : AlgebraicSpace S) : (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  (Over.forget X).op ⋙ gammaFunctor

/-- On `U ⟶ X`, the big étale structure presheaf has value `Γ(U, 𝒪_U)`. -/
theorem structurePresheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (structurePresheaf X).obj (op U) = gamma U.left :=
  rfl

/-- Restriction in `structurePresheaf X` is `gammaMap` of the underlying morphism of algebraic
spaces. -/
theorem structurePresheaf_map {X : AlgebraicSpace S} {U V : Over X} (g : U ⟶ V) :
    (structurePresheaf X).map g.op = gammaMap g.left :=
  rfl

/-- The presheaf `U ↦ Γ(U, 𝒪_U)` on `(Spaces/X)_étale` is a sheaf, since `𝒪_U` is a sheaf on
the étale site of `U`. -/
theorem structurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (overEtaleTopology X) (structurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪` on the big étale site `(Spaces/X)_étale`. -/
def structureSheaf (X : AlgebraicSpace S) : Sheaf (overEtaleTopology X) RingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

/-- On `U ⟶ X`, the big étale structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem structureSheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (structureSheaf X).obj.obj (op U) = gamma U.left :=
  rfl

/-- Restriction in `structureSheaf X` is `gammaMap` of the underlying morphism of algebraic
spaces. -/
theorem structureSheaf_map {X : AlgebraicSpace S} {U V : Over X} (g : U ⟶ V) :
    (structureSheaf X).obj.map g.op = gammaMap g.left :=
  rfl

/-- Ring-valued sheaves on `(Spaces/X)_étale` compose with the forgetful functor to types. -/
instance overEtaleTopology_hasSheafCompose_forgetRingCat (X : AlgebraicSpace S) :
    (overEtaleTopology X).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The big étale ringed site `((Spaces/X)_étale, 𝒪)`. -/
abbrev ringedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (overEtaleTopology X) (structureSheaf X)

/-- The structure sheaf of `ringedSite X` is `structureSheaf X`. -/
theorem ringedSite_structureSheaf (X : AlgebraicSpace S) :
    (ringedSite X).structureSheaf = structureSheaf X :=
  rfl

/-- The site topology of `ringedSite X` is `overEtaleTopology X`. -/
theorem ringedSite_siteTopology (X : AlgebraicSpace S) :
    (ringedSite X).siteTopology = overEtaleTopology X :=
  rfl

/-- The diagonal morphism `U ⟶ U ×_Y U` in `U_spaces,étale`. -/
def diagonalToPullback {Y : AlgebraicSpace S} (U : spacesEtaleSite Y) :
    spacesEtaleSite.self U.left ⟶ (spacesEtalePullback U.hom).obj U :=
  MorphismProperty.Over.homMk (pullback.diagonal U.hom) sorry

/-- The left component of `diagonalToPullback U` is `pullback.diagonal U.hom`. -/
theorem diagonalToPullback_left {Y : AlgebraicSpace S} (U : spacesEtaleSite Y) :
    (diagonalToPullback U).left = pullback.diagonal U.hom :=
  rfl

/-- Comparison `𝒪_Y(U) ⟶ Γ(U, 𝒪_U)` on the spaces-étale site, obtained by pulling functions
back to `U ×_Y U` and restricting along the diagonal. -/
def spacesStructureToGamma {Y : AlgebraicSpace S} (U : spacesEtaleSite Y) :
    (spacesStructureSheaf Y).obj.obj (op U) ⟶ gamma U.left :=
  (spacesStructureSheafMap U.hom).hom.app (op U) ≫
    (spacesStructureSheaf U.left).obj.map (op (diagonalToPullback U))

/-- `spacesStructureToGamma U` is `spacesStructureSheafMap U.hom` at `U`, followed by
restriction along the diagonal. -/
theorem spacesStructureToGamma_eq {Y : AlgebraicSpace S} (U : spacesEtaleSite Y) :
    spacesStructureToGamma U =
      (spacesStructureSheafMap U.hom).hom.app (op U) ≫
        (spacesStructureSheaf U.left).obj.map (op (diagonalToPullback U)) :=
  rfl

/-- The comparison `𝒪_Y(U) ⟶ Γ(U, 𝒪_U)` is an isomorphism of rings. -/
instance spacesStructureToGamma_isIso {Y : AlgebraicSpace S} (U : spacesEtaleSite Y) :
    IsIso (spacesStructureToGamma U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
