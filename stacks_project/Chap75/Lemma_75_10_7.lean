module

public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Lemma_75_10_4_HomSequence
public import stacks_project.Chap75.Lemma_75_10_7_Comparison

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

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}

/-- Lemma 75.10.7 (1). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `E` is an object
of `D(𝒪_X)` supported on `T`, then the canonical map `E ⟶ Rf_*(E|_V)` of source (1)(a) is
an isomorphism. -/
@[stacks 08GG]
theorem isIso_restrictPushforwardDerived_unit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ) :
    IsIso ((restrictPushforwardDerivedAdjunction f).unit.app E) :=
  sorry

/-- Lemma 75.10.7 (2). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `E` is an object
of `D(𝒪_X)` supported on `T`, then the canonical map `f_!(E|_V) ⟶ E` of source (1)(b) is an
isomorphism. -/
@[stacks 08GG]
theorem isIso_lowerShriekDerived_counit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (E : ModuleDerived X)
    (hE : IsSupportedOn E (toOpenSubspace j f).pointsSetᶜ) :
    IsIso ((lowerShriekDerivedAdjunction f).counit.app E) :=
  sorry

/-- Lemma 75.10.7 (3). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then the canonical map `F ⟶ (f_! F)|_V` of source (2)(a)
is an isomorphism. -/
@[stacks 08GG]
theorem isIso_lowerShriekDerived_unit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsIso ((lowerShriekDerivedAdjunction f).unit.app F) :=
  sorry

/-- Lemma 75.10.7 (4). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then the canonical map `(Rf_* F)|_V ⟶ F` of source (2)(b)
is an isomorphism. -/
@[stacks 08GG]
theorem isIso_restrictPushforwardDerived_counit (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsIso ((restrictPushforwardDerivedAdjunction f).counit.app F) :=
  sorry

/-- Lemma 75.10.7 (5). Let `S` be a scheme. Let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Set `T = |X| \ |U|`. If `F` is an object
of `D(𝒪_V)` supported on `f⁻¹T`, then `f_! F` and `Rf_* F` are isomorphic, corresponding
to source (2)(c). -/
@[stacks 08GG]
theorem nonempty_iso_lowerShriekDerived_pushforwardDerived (j : U ⟶ X) [Etale j]
    (f : V ⟶ X) [Etale f] [IsElementaryDistinguishedSquare j f] (F : ModuleDerived V)
    (hF : IsSupportedOn F (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    Nonempty ((lowerShriekDerived f).obj F ≅ (pushforwardDerived f).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
