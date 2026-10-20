module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Artinian.Local
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.Objects

/-! The Rim-Schlessinger condition for set-valued functors on locally Noetherian schemes. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite ObjectProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Over

section Comparison

variable {S : Scheme.{u}}
variable (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
variable {X X' Y Y' : Over S}
variable [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
  [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
variable [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
  [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
variable {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
variable [IsClosedImmersion toX'.left]

/-- The two restrictions of a value of `F` on a pushout agree over `X`. -/
theorem comparison_comp (h : IsPushout toX' toY fromX' fromY)
    (ξ : F.obj (op (asLocallyNoetherian Y'))) :
    F.map (op (asLocallyNoetherianMap toY))
        (F.map (op (asLocallyNoetherianMap fromY)) ξ) =
      F.map (op (asLocallyNoetherianMap toX'))
        (F.map (op (asLocallyNoetherianMap fromX')) ξ) := sorry

/-- The set-level Rim-Schlessinger comparison
`F(Y') → F(Y) ×_{F(X)} F(X')` associated to a pushout
`Y' = Y ⨿_X X'` in `Over S`. -/
def comparison (h : IsPushout toX' toY fromX' fromY) :
    F.obj (op (asLocallyNoetherian Y')) →
      Types.PullbackObj (F.map (op (asLocallyNoetherianMap toY)))
        (F.map (op (asLocallyNoetherianMap toX'))) :=
  fun ξ ↦ ⟨⟨F.map (op (asLocallyNoetherianMap fromY)) ξ,
      F.map (op (asLocallyNoetherianMap fromX')) ξ⟩, comparison_comp F h ξ⟩

/-- The first projection of `comparison F h` is restriction along `fromY`. -/
theorem comparison_fst (h : IsPushout toX' toY fromX' fromY)
    (ξ : F.obj (op (asLocallyNoetherian Y'))) :
    (comparison F h ξ).1.1 = F.map (op (asLocallyNoetherianMap fromY)) ξ :=
  sorry

/-- The second projection of `comparison F h` is restriction along `fromX'`. -/
theorem comparison_snd (h : IsPushout toX' toY fromX' fromY)
    (ξ : F.obj (op (asLocallyNoetherian Y'))) :
    (comparison F h ξ).1.2 = F.map (op (asLocallyNoetherianMap fromX')) ξ :=
  sorry

end Comparison

/-- A Type-valued functor on locally Noetherian schemes over a locally Noetherian
base `S` satisfies condition (RS) if for every pushout `Y' = Y ⨿_X X'` in
`Over S` whose vertices are spectra of local Artinian rings, of finite type over
`S`, and with `X ⟶ X'` a closed immersion, the comparison
`F(Y') → F(Y) ×_{F(X)} F(X')` is a bijection. -/
class HasRimSchlessinger {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) : Prop where
  /-- Restriction along an Artinian finite-type closed-immersion pushout is a
  bijection of value types. -/
  bijective_comparison :
    ∀ {X X' Y Y' : Over S}
      [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
      [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
      [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
      [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
      {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
      [IsClosedImmersion toX'.left]
      (h : IsPushout toX' toY fromX' fromY),
      Function.Bijective (comparison F h)

/-- Condition (RS) is equivalent to bijectivity of `comparison` on every Artinian
finite-type closed-immersion pushout in `Over S`. -/
theorem hasRimSchlessinger_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) :
    HasRimSchlessinger F ↔
      ∀ {X X' Y Y' : Over S}
        [IsSpecLocalArtinian X.left] [IsSpecLocalArtinian X'.left]
        [IsSpecLocalArtinian Y.left] [IsSpecLocalArtinian Y'.left]
        [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType X'.hom]
        [Scheme.Hom.FiniteType Y.hom] [Scheme.Hom.FiniteType Y'.hom]
        {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
        [IsClosedImmersion toX'.left]
        (h : IsPushout toX' toY fromX' fromY),
        Function.Bijective (comparison F h) := sorry

/-- A representable functor restricted to locally Noetherian schemes satisfies
Rim-Schlessinger, since morphisms out of a pushout are compatible pairs. -/
instance instHasRimSchlessinger_restrictedYoneda {S : Scheme.{u}}
    [IsLocallyNoetherian S] (U : Over S) :
    HasRimSchlessinger ((locallyNoetherian S).ι.op ⋙ yoneda.obj U) := sorry

end AlgebraicGeometry.Scheme.Over
