/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison

/-!
# Scheme-theoretic support of a module on an algebraic space

A closed immersion `i : Z ⟶ X` is a scheme-theoretic support of a module `F`
when `F` is the pushforward of a quasi-coherent module from `Z`, and `i` is
least among closed immersions with that property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` associated to a closed subscheme of a scheme
over `S`. -/
def ofOverClosedSubscheme {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) : AlgebraicSpace S :=
  ofOver (Over.mk (I.subschemeι ≫ U.hom))

/-- The inclusion of a closed subscheme of `U`, as a morphism of algebraic spaces
over `S`. -/
def ofOverClosedSubschemeι {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) :
    ofOverClosedSubscheme U I ⟶ ofOver U :=
  ofOverMap (Over.homMk I.subschemeι rfl)

/-- `ofOverClosedSubscheme U I` is `ofOver` of the structure morphism of `I.subscheme`,
and `ofOverClosedSubschemeι U I` is the corresponding `ofOverMap`. -/
theorem ofOverClosedSubscheme_spec {S : Scheme.{u}} (U : Over S)
    (I : U.left.IdealSheafData) :
    ofOverClosedSubscheme U I = ofOver (Over.mk (I.subschemeι ≫ U.hom)) ∧
      ofOverClosedSubschemeι U I = ofOverMap (Over.homMk I.subschemeι rfl) :=
  sorry

namespace Modules

/-- The scheme-theoretic support of the restriction to a scheme `U` of an étale
pullback of an `𝒪_X`-module. -/
def etalePullbackSchemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X) : U.left.IdealSheafData :=
  Scheme.Modules.schemeTheoreticSupport ((restrictToScheme U).obj ((pullback φ).obj F))

/-- `etalePullbackSchemeTheoreticSupport F φ` is the scheme-theoretic support of
the restriction of `φ* F` to `U`. -/
theorem etalePullbackSchemeTheoreticSupport_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (F : X.Modules) (φ : ofOver U ⟶ X) :
    etalePullbackSchemeTheoreticSupport F φ =
      Scheme.Modules.schemeTheoreticSupport
        ((restrictToScheme U).obj ((pullback φ).obj F)) :=
  sorry

/-- A closed immersion `i : Z ⟶ X` is a scheme-theoretic support of `F` if `F`
is the pushforward of a quasi-coherent `𝒪_Z`-module and `i` is least among
closed immersions with that property. -/
class IsSchemeTheoreticSupport {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X) : Prop where
  /-- The comparison `i : Z ⟶ X` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- There is a quasi-coherent `𝒪_Z`-module whose pushforward is isomorphic to `F`. -/
  exists_quasicoherent :
    ∃ G : Z.Modules, G.IsQuasicoherent ∧ Nonempty ((pushforward i).obj G ≅ F)
  /-- Any other closed immersion through which `F` is a quasi-coherent pushforward
  admits a unique comparison from `Z`. -/
  exists_lift {Z' : AlgebraicSpace S} (i' : Z' ⟶ X) [IsClosedImmersion i']
      (h : ∃ G' : Z'.Modules,
        G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) :
      ∃! k : Z ⟶ Z', k ≫ i' = i

/-- A scheme-theoretic support of `F` is a closed immersion. -/
theorem isClosedImmersion {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    {F : X.Modules} {i : Z ⟶ X} [IsSchemeTheoreticSupport F i] :
    IsClosedImmersion i :=
  sorry

/-- A morphism `i : Z ⟶ X` is a scheme-theoretic support of `F` if and only if it
is a least closed immersion through which `F` is a quasi-coherent pushforward. -/
theorem isSchemeTheoreticSupport_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (F : X.Modules) (i : Z ⟶ X) :
    IsSchemeTheoreticSupport F i ↔
      IsClosedImmersion i ∧
        (∃ G : Z.Modules, G.IsQuasicoherent ∧ Nonempty ((pushforward i).obj G ≅ F)) ∧
          ∀ {Z' : AlgebraicSpace S} (i' : Z' ⟶ X) [IsClosedImmersion i'],
            (∃ G' : Z'.Modules,
              G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) →
              ∃! k : Z ⟶ Z', k ≫ i' = i :=
  sorry

namespace IsSchemeTheoreticSupport

/-- The comparison from a scheme-theoretic support through any other closed
immersion carrying a quasi-coherent descent of `F` is unique. -/
theorem lift {S : Scheme.{u}} {X Z : AlgebraicSpace S} {F : X.Modules}
    {i : Z ⟶ X} [IsSchemeTheoreticSupport F i] {Z' : AlgebraicSpace S}
    (i' : Z' ⟶ X) [IsClosedImmersion i']
    (h : ∃ G' : Z'.Modules,
      G'.IsQuasicoherent ∧ Nonempty ((pushforward i').obj G' ≅ F)) :
    ∃! k : Z ⟶ Z', k ≫ i' = i :=
  sorry

/-- A least closed-subspace factorization through which `F` is a quasi-coherent
pushforward is a scheme-theoretic support. -/
theorem of_isLeast_closedSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (Z : ClosedSubspace X)
    (hQC : ∃ G : Z.X.Modules,
      G.IsQuasicoherent ∧ Nonempty ((pushforward Z.ι).obj G ≅ F))
    (hleast : ∀ Z' : ClosedSubspace X,
      (∃ G' : Z'.X.Modules,
        G'.IsQuasicoherent ∧ Nonempty ((pushforward Z'.ι).obj G' ≅ F)) →
        ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) :
    IsSchemeTheoreticSupport F Z.ι :=
  sorry

end IsSchemeTheoreticSupport

/-- Two quasi-coherent modules on a closed subspace with chosen pushforward
identifications to `F` admit a unique isomorphism compatible with those
identifications. -/
theorem existsUnique_iso_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {F : X.Modules} (i : Z ⟶ X) [IsClosedImmersion i]
    (G G' : Z.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) (e' : (pushforward i).obj G' ≅ F) :
    ∃! α : G ≅ G', ((pushforward i).mapIso α).trans e' = e :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
