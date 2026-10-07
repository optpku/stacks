module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_22_7_Neighbourhood

/-!
# Lemma 81.10.3

The étale geometric stalk of the pushforward of a quasi-coherent module along a
quasi-compact and quasi-separated morphism of algebraic spaces is the module of
sections of the pullback to the fibre product with `Spec` of the étale local ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Global sections of `p^* G` on the fibre product
`Y ×_X Spec(etaleLocalRing X xbar)`, as a module over `etaleLocalRing X xbar`.
Here `p = Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)` is the projection
to `Y`, and the module structure is affine `Γ` of `q_* p^* G` on
`Spec(etaleLocalRing X xbar)` with
`q = Limits.pullback.snd f (fromSpecEtaleLocalRing xbar)`. -/
def sectionsOverEtaleLocalRing {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (xbar : GeometricPoint X) (G : Y.Modules) :
    ModuleCat (etaleLocalRing X xbar) :=
  (pullback (Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)) ⋙
      pushforward (Limits.pullback.snd f (fromSpecEtaleLocalRing xbar)) ⋙
      toScheme (Over.mk (specHom xbar)) ⋙
      @moduleSpecΓFunctor (CommRingCat.of (etaleLocalRing X xbar))).obj G

/-- `sectionsOverEtaleLocalRing` is affine `Γ` of `q_* p^* G` on
`Spec(etaleLocalRing X xbar)`. -/
theorem sectionsOverEtaleLocalRing_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (xbar : GeometricPoint X) (G : Y.Modules) :
    sectionsOverEtaleLocalRing f xbar G =
      (pullback (Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)) ⋙
          pushforward (Limits.pullback.snd f (fromSpecEtaleLocalRing xbar)) ⋙
          toScheme (Over.mk (specHom xbar)) ⋙
          @moduleSpecΓFunctor (CommRingCat.of (etaleLocalRing X xbar))).obj G :=
  rfl

/-- Lemma 81.10.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`f : Y ⟶ X` be a quasi-compact and quasi-separated morphism. Let `xbar` be a
geometric point of `X` and let `fromSpecEtaleLocalRing xbar` be the canonical
morphism `Spec(etaleLocalRing X xbar) ⟶ X`. For a quasi-coherent module `G` on
`Y`, the étale stalk `stalkModuleCat xbar ((pushforward f).obj G)` is isomorphic
to `sectionsOverEtaleLocalRing f xbar G`, i.e. to
`Γ(Y ×_X Spec(etaleLocalRing X xbar), p^* G)` where
`p = Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)`. -/
@[stacks 0AES]
theorem pushforward_stalk_iso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] (xbar : GeometricPoint X)
    (G : Y.Modules) [G.IsQuasicoherent] :
    IsIsomorphic (stalkModuleCat xbar ((pushforward f).obj G))
      (sectionsOverEtaleLocalRing f xbar G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

