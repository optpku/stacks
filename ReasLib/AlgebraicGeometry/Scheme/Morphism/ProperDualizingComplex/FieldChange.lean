/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/-- If a proper morphism from a scheme to the spectrum of a field factors through the spectrum
of another field, then the factored morphism is proper. -/
theorem isProper_ofFieldFactorization
    {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (f' : X ⟶ Spec (CommRingCat.of k'))
    (g : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
    (hfactor : f' ≫ g = f) :
    IsProper f' := sorry

/-- If a proper morphism from a scheme to the spectrum of a field factors through the spectrum
of another field, then the chosen proper dualizing complex and dualizing module of the original
morphism are isomorphic to those of the factored morphism. -/
theorem ofFieldFactorization
    {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (f' : X ⟶ Spec (CommRingCat.of k')) [IsProper f']
    (g : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
    (hfactor : f' ≫ g = f) :
    IsIsomorphic (properDualizingComplex f) (properDualizingComplex f') ∧
      IsIsomorphic (dualizingModule f) (dualizingModule f') := sorry

/-- After a field extension, derived pullback of the chosen proper dualizing complex and ordinary
pullback of the dualizing module agree up to isomorphism with the corresponding objects of the
base-changed structure morphism. -/
theorem baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
    IsIsomorphic
        ((DerivedQCoh.pullback (pullback.fst f g)).obj (properDualizingComplex f))
        (properDualizingComplex (pullback.snd f g)) ∧
      IsIsomorphic
        ((Scheme.Modules.pullback (pullback.fst f g)).obj (dualizingModule f))
        (dualizingModule (pullback.snd f g)) := sorry

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
