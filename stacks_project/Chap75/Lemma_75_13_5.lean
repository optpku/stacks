module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

universe u

/- Lemma 75.13.5: for a scheme `X` and `E` in `D(𝒪_X)`, `E` is a perfect
object of `D(𝒪_X)` if and only if `ε* E` is a perfect object of
`D(𝒪_étale)`, where `ε` is `commSmallEtaleToZariski`, the commutative
universe-lifted form of `smallEtaleToZariski` as in 75.4.0.1. -/
@[stacks 08HG] #check
  (AlgebraicGeometry.Scheme.SiteRestriction.commSmallEtaleToZariski_isPerfect_iff :
    ∀ {X : Scheme.{u}}
      (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)),
      E.IsPerfect ↔
        ((commSmallEtaleToZariskiDerived X).obj E).IsPerfect)

