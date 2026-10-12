/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

/- Lemma 58.16.3: for a proper morphism with geometrically connected fibres, every
specialization map along `sbar' ⤳ sbar` is isomorphic to the specialization map induced
by a strictly henselian valuation ring over `S` with algebraically closed fraction field. -/
@[stacks 0C0M] #check (EtaleFundamentalGroup.IsSpecializationMap.exists_strictHenselianValuationRing :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp),
    ∃ (D : _root_.Specializes.ValuationRealization sbar'.toFieldValuedPoint.image
        sbar.toFieldValuedPoint.image (sbar'.toFieldValuedPoint.residueFieldHom))
      (Rsh : Type u) (_ : CommRing Rsh)
      (_ : Algebra (S.presheaf.stalk sbar.image) Rsh)
      (_ : IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh)
      (strictToField : Rsh →+* sbar'.toFieldValuedPoint.K)
      (e' : Aut F' ≃* Aut F') (e : Aut F ≃* Aut F),
      EtaleFundamentalGroup.IsSpecializationMap.valuationInduced f sbar' sbar hSpec F' F sp hsp D Rsh strictToField e' e)
