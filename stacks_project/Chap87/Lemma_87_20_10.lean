/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_20_10_Types

/-!
# Fibre products of locally typed formal algebraic spaces

Local countably indexed, locally countably indexed and classical, locally
weakly adic, locally adic*, and locally Noetherian types of formal algebraic
spaces are stable under fibre products. The locally Noetherian case requires
the induced map of reductions `X_red ⟶ Y_red` to be locally of finite type
as a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A morphism of sheaves on `(Sch/S)_fppf` is locally of finite type in the
algebraic-space sense when every commutative square against it with étale
vertical arrows from sheafified representables has locally-of-finite-type top
arrow. This does not require the morphism to be representable by schemes. -/
def locallyOfFiniteTypeOnEtaleSquares {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ {U V : 𝒮.bigSite S}
    (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
    relativelyEtale a → relativelyEtale b →
      a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b →
        LocallyOfFiniteType ((𝒮.bigToScheme S).map h)

/-- Algebraic-space local finite type unpacks as local finite type of the top
arrow of every étale scheme square. -/
theorem locallyOfFiniteTypeOnEtaleSquares_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    locallyOfFiniteTypeOnEtaleSquares f ↔
      ∀ {U V : 𝒮.bigSite S}
        (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
        relativelyEtale a → relativelyEtale b →
          a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b →
            LocallyOfFiniteType ((𝒮.bigToScheme S).map h) :=
  sorry

/-- Algebraic-space local finite type implies local finite type of the top
arrow of any étale scheme square. -/
theorem locallyOfFiniteTypeOnEtaleSquares_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : locallyOfFiniteTypeOnEtaleSquares f) {U V : 𝒮.bigSite S}
    (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V)
    (ha : relativelyEtale a) (hb : relativelyEtale b)
    (hsq : a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableMap h ≫ b) :
    LocallyOfFiniteType ((𝒮.bigToScheme S).map h) :=
  sorry

/-- Lemma 87.20.10 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `X` and `Z` are locally
countably indexed, then so is `pullback f g`. -/
@[stacks 0GBB]
instance instIsLocallyCountablyIndexed_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyCountablyIndexed X]
    [IsLocallyCountablyIndexed Z] (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] :
    IsLocallyCountablyIndexed (pullback f g) :=
  sorry

/-- Lemma 87.20.10 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `X` and `Z` are locally
countably indexed and classical, then so is `pullback f g`. -/
@[stacks 0GBB]
instance instIsLocallyClassical_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyClassical X] [IsLocallyClassical Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] :
    IsLocallyClassical (pullback f g) :=
  sorry

/-- Lemma 87.20.10 (3): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `X` and `Z` are weakly adic
in the sense of locally weakly adic, then so is `pullback f g`. -/
@[stacks 0GBB]
instance instIsLocallyWeaklyAdic_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyWeaklyAdic X] [IsLocallyWeaklyAdic Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] :
    IsLocallyWeaklyAdic (pullback f g) :=
  sorry

/-- Lemma 87.20.10 (4): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `X` and `Z` are locally
adic*, then so is `pullback f g`. -/
@[stacks 0GBB]
instance instIsLocallyAdicStar_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsLocallyAdicStar X] [IsLocallyAdicStar Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] :
    IsLocallyAdicStar (pullback f g) :=
  sorry

/-- Lemma 87.20.10 (5): Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `X` and `Z` are locally
Noetherian and `X_red ⟶ Y_red` is locally of finite type as a morphism of
algebraic spaces, then `pullback f g` is locally Noetherian. -/
@[stacks 0GBB]
theorem instIsLocallyNoetherian_pullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace.IsLocallyNoetherian X]
    [IsFormalAlgebraicSpace.IsLocallyNoetherian Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [HasPullback f g]
    (φ : IsFormalAlgebraicSpace.reduction X ⟶ IsFormalAlgebraicSpace.reduction Y)
    (hφ : φ ≫ IsFormalAlgebraicSpace.reductionι Y =
      IsFormalAlgebraicSpace.reductionι X ≫ f)
    (hft : locallyOfFiniteTypeOnEtaleSquares φ) :
    IsFormalAlgebraicSpace.IsLocallyNoetherian (pullback f g) :=
  sorry

end AlgebraicGeometry
