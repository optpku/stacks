/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Noetherian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat

/- Lemma 56.4.6 (1): a functor between finitely generated modules over Noetherian
rings extends uniquely, compatibly up to natural isomorphism, preserving filtered colimits. -/
@[stacks 0GP9] #check
  (ModuleCat.fgFilteredColimitExtension_existsUnique :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B),
    ∃ (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
      (eF' : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
      (_ : PreservesFilteredColimitsOfSize.{max u v, max u v} F'),
      ∀ (G : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
        (eG : (isFG.{max u v} A).ι ⋙ G ≅ F ⋙ (isFG.{max u v} B).ι),
        PreservesFilteredColimitsOfSize.{max u v, max u v} G →
          ∃! α : F' ≅ G,
            Functor.isoWhiskerLeft (isFG.{max u v} A).ι α ≪≫ eG = eF')

/- Lemma 56.4.6 (2): if `F` is additive, then the filtered-colimit-preserving
extension `F'` is additive. -/
@[stacks 0GP9] #check
  (ModuleCat.fgFilteredColimitExtension_additive :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'],
    F'.Additive)

/- Lemma 56.4.6 (3): if `F` is additive, then `F'` commutes with arbitrary
direct sums. -/
@[stacks 0GP9] #check
  (ModuleCat.fgFilteredColimitExtension_preservesCoproducts :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [F.Additive]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (J : Type (max u v)),
    PreservesColimitsOfShape (Discrete J) F')

/- Lemma 56.4.6 (4): if `F` is right exact, then so is `F'`. In particular, if `F`
is exact then `F'` is right exact. -/
@[stacks 0GP9] #check
  (ModuleCat.fgFilteredColimitExtension_preservesFiniteColimits :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [PreservesFiniteColimits F]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'],
    PreservesFiniteColimits F')

/- Lemma 56.4.6 (5): if `F` is left exact, then so
is `F'`. In particular, if `F` is exact then `F'` is left exact. -/
@[stacks 0GP9] #check
  (ModuleCat.fgFilteredColimitExtension_preservesFiniteLimits :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [CommRing B] [IsNoetherianRing B]
    (F : FGModuleCat.{max u v} A ⥤ FGModuleCat.{max u v} B)
    [PreservesFiniteLimits F]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (isFG.{max u v} A).ι ⋙ F' ≅ F ⋙ (isFG.{max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'],
    PreservesFiniteLimits F')

end ModuleCat
