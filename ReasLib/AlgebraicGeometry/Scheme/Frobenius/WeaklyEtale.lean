/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.UniversalHomeomorphism

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative Frobenius of a weakly étale morphism in prime characteristic is weakly
étale. -/
instance relativeFrobenius_weaklyEtale {p : ℕ} [Fact p.Prime] {U X : Scheme.{u}}
    (f : U ⟶ X) [Scheme.IsCharP X p] [WeaklyEtale f] :
    WeaklyEtale (relativeFrobenius (p := p) f) := sorry

/-- The relative Frobenius of a weakly étale morphism in prime characteristic is an
isomorphism. -/
instance relativeFrobenius_isIso {p : ℕ} [Fact p.Prime] {U X : Scheme.{u}}
    (f : U ⟶ X) [Scheme.IsCharP X p] [WeaklyEtale f] :
    IsIso (relativeFrobenius (p := p) f) := sorry

end AlgebraicGeometry.Scheme.Hom
