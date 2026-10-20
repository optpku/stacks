module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Geometric stalks of direct images of modules

For a quasi-compact and quasi-separated morphism of algebraic spaces, the geometric
stalk of the direct image of a quasi-coherent module is its module of sections
after base change to the spectrum of the étale local ring.
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
      moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing X xbar))).obj G

/-- `sectionsOverEtaleLocalRing` is affine `Γ` of `q_* p^* G` on
`Spec(etaleLocalRing X xbar)`. -/
theorem sectionsOverEtaleLocalRing_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (xbar : GeometricPoint X) (G : Y.Modules) :
    sectionsOverEtaleLocalRing f xbar G =
      (pullback (Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)) ⋙
          pushforward (Limits.pullback.snd f (fromSpecEtaleLocalRing xbar)) ⋙
          toScheme (Over.mk (specHom xbar)) ⋙
          moduleSpecΓFunctor (R := CommRingCat.of (etaleLocalRing X xbar))).obj G :=
  rfl

/-- Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`f : Y ⟶ X` be a quasi-compact and quasi-separated morphism. Let `xbar` be a
geometric point of `X` and let `fromSpecEtaleLocalRing xbar` be the canonical
morphism `Spec(etaleLocalRing X xbar) ⟶ X`. For a quasi-coherent module `G` on
`Y`, the étale stalk `stalkModuleCat xbar ((pushforward f).obj G)` is isomorphic
to `sectionsOverEtaleLocalRing f xbar G`, i.e. to
`Γ(Y ×_X Spec(etaleLocalRing X xbar), p^* G)` where
`p = Limits.pullback.fst f (fromSpecEtaleLocalRing xbar)`. -/
theorem pushforward_stalk_iso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] (xbar : GeometricPoint X)
    (G : Y.Modules) [G.IsQuasicoherent] :
    IsIsomorphic (stalkModuleCat xbar ((pushforward f).obj G))
      (sectionsOverEtaleLocalRing f xbar G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
