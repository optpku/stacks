/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Support

/-!
# Support-conditional isomorphisms for étale restriction, lower shriek, and pushforward

On an elementary distinguished square, complexes supported on the complement of `U` (resp.
its preimage) make the derived unit and counit of `f^* ⊣ Rf_*` and `f_! ⊣ f^*`
isomorphisms, and identify `f_!` with `Rf_*` on that support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

noncomputable section

universe u

/- Lemma 75.10.7 (1). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `E` is an object
of `D(𝒪_X)` supported on `T`, then the canonical map `E ⟶ Rf_*(E|_V)` of source (1)(a) is
an isomorphism. -/
@[stacks 08GG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_restrictPushforwardDerived_unit :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ),
    IsIso ((restrictPushforwardDerivedAdjunction f).unit.app E))

/- Lemma 75.10.7 (2). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `E` is an object
of `D(𝒪_X)` supported on `T`, then the canonical map `f_!(E|_V) ⟶ E` of source (1)(b) is an
isomorphism. -/
@[stacks 08GG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_lowerShriekDerived_counit :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ),
    IsIso ((lowerShriekDerivedAdjunction f).counit.app E))

/- Lemma 75.10.7 (3). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then the canonical map `F ⟶ (f_! F)|_V` of source (2)(a)
is an isomorphism. -/
@[stacks 08GG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_lowerShriekDerived_unit :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)),
    IsIso ((lowerShriekDerivedAdjunction f).unit.app F))

/- Lemma 75.10.7 (4). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then the canonical map `(Rf_* F)|_V ⟶ F` of source (2)(b)
is an isomorphism. -/
@[stacks 08GG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_restrictPushforwardDerived_counit :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)),
    IsIso ((restrictPushforwardDerivedAdjunction f).counit.app F))

/- Lemma 75.10.7 (5). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then the canonical comparison `f_! F ⟶ Rf_* F` is an isomorphism,
corresponding to source (2)(c). Its transpose is the two-sided inverse of the lower-shriek unit. -/
@[stacks 08GG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.existsUnique_lowerShriekDerived_pushforwardDerived_comparison :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)),
    ∃! c : (lowerShriekDerived f).obj F ⟶ (moduleDerivedPushforward f).obj F,
      let a := ((restrictPushforwardDerivedAdjunction f).homEquiv
        ((lowerShriekDerived f).obj F) F).symm c
      ((lowerShriekDerivedAdjunction f).unit.app F ≫ a = 𝟙 F) ∧
        (a ≫ (lowerShriekDerivedAdjunction f).unit.app F =
          𝟙 ((restrictFunctorDerived f).obj ((lowerShriekDerived f).obj F))) ∧
        IsIso c)
