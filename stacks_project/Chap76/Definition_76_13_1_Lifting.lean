/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over

#check (AlgebraicGeometry.Scheme.Over.liftPair :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) →
      {T T' : Over S} → (T ⟶ T') → F.obj (op T') → F.obj (op T) × G.obj (op T'))

#check (AlgebraicGeometry.Scheme.Over.liftPair_apply :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')),
      liftPair a i x' = (F.map (op i) x', a.app (op T') x'))

#check (AlgebraicGeometry.Scheme.Over.liftPair_fst :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')),
      (liftPair a i x').1 = F.map (op i) x')

#check (AlgebraicGeometry.Scheme.Over.liftPair_snd :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    {T T' : Over S} (i : T ⟶ T') (x' : F.obj (op T')),
      (liftPair a i x').2 = a.app (op T') x')

#check (AlgebraicGeometry.Scheme.Over.FormallySmooth :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)

#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)

#check (AlgebraicGeometry.Scheme.Over.formallySmooth_iff :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G),
      FormallySmooth a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map (op i) y → ∃ x' : F.obj (op T'), liftPair a i x' = (x, y))

#check (AlgebraicGeometry.Scheme.Over.formallyEtale_iff :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G),
      FormallyEtale a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map (op i) y → ∃! x' : F.obj (op T'), liftPair a i x' = (x, y))

#check (AlgebraicGeometry.Scheme.Over.formallyUnramified_iff :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G),
      FormallyUnramified a ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left], Function.Injective (liftPair a i))

#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.id :
    ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v),
      FormallySmooth (𝟙 F))

#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.hasLiftingProperty :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallySmooth a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left],
      HasLiftingProperty (yoneda.map i) a)

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.id :
    ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v),
      FormallyEtale (𝟙 F))

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.toFormallySmooth :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a],
      FormallySmooth a)

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.toFormallyUnramified :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} [FormallyEtale a],
      FormallyUnramified a)

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.iff_formallySmooth_and_formallyUnramified :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} (a : F ⟶ G),
      FormallyEtale a ↔ FormallySmooth a ∧ FormallyUnramified a)

#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.existsUnique_liftStruct :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyEtale a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g),
      Nonempty (Unique sq.LiftStruct))

#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.id :
    ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v),
      FormallyUnramified (𝟙 F))

#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.hom_ext :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G}
    [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {x₁ x₂ : F.obj (op T')},
      liftPair a i x₁ = liftPair a i x₂ → x₁ = x₂)

#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.subsingleton_liftStruct :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [FormallyUnramified a] {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left] {f : yoneda.obj T ⟶ F}
    {g : yoneda.obj T' ⟶ G} (sq : CommSq f (yoneda.map i) a g),
      Subsingleton sq.LiftStruct)

end AlgebraicGeometry.Scheme.Over
