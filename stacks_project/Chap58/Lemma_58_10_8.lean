module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FiniteClosedComplement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.PuncturedSpectrum
open AlgebraicGeometry.Scheme

universe u v w

/- Lemma 58.10.8 (1) -/
@[stacks 0BSC] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.surjective_of_finiteClosedComplement :
    ∀ {X : Scheme.{u}} {ι : Type v} [Finite ι] (x : ι → X),
      (∀ i, IsClosed ({x i} : Set X)) → ∀ (U : X.Opens),
      (U : Set X) = (Set.range x)ᶜ → [ConnectedSpace U] →
      IsRetrocompact (U : Set X) → ∀ (Ash : ι → Type u),
      [∀ i, CommRing (Ash i)] →
      [∀ i, Algebra (X.presheaf.stalk (x i)) (Ash i)] →
      [∀ i, IsStrictHenselizationOf (X.presheaf.stalk (x i)) (Ash i)] →
      [∀ i, ConnectedSpace (PuncturedSpectrum.scheme (Ash i))] →
      ∀ (FX : FiniteEtale X ⥤ FintypeCat.{w}),
      [GaloisCategory (FiniteEtale X)] → [FiberFunctor FX] →
      ∀ (FU : FiniteEtale (U : Scheme.{u}) ⥤ FintypeCat.{w}),
      [GaloisCategory (FiniteEtale (U : Scheme.{u}))] → [FiberFunctor FU] →
      ∀ (h : ContinuousMonoidHom (Aut FU) (Aut FX)),
      CatCommSq (finiteEtaleBaseChange U.ι) (functorToAction FX)
        (functorToAction FU) (Action.res FintypeCat h.toMonoidHom) →
      Function.Surjective h)

/- Lemma 58.10.8 (2) -/
@[stacks 0BSC] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.ker_of_finiteClosedComplement :
    ∀ {X : Scheme.{u}} {ι : Type v} [Finite ι] (x : ι → X)
      (hx : ∀ i, IsClosed ({x i} : Set X)) (U : X.Opens)
      (hUeq : (U : Set X) = (Set.range x)ᶜ) [ConnectedSpace U]
      (hretro : IsRetrocompact (U : Set X)) (Ash : ι → Type u)
      [∀ i, CommRing (Ash i)]
      [∀ i, Algebra (X.presheaf.stalk (x i)) (Ash i)]
      [∀ i, IsStrictHenselizationOf (X.presheaf.stalk (x i)) (Ash i)]
      [∀ i, ConnectedSpace (PuncturedSpectrum.scheme (Ash i))]
      (FX : FiniteEtale X ⥤ FintypeCat.{w})
      [GaloisCategory (FiniteEtale X)] [FiberFunctor FX]
      (FU : FiniteEtale (U : Scheme.{u}) ⥤ FintypeCat.{w})
      [GaloisCategory (FiniteEtale (U : Scheme.{u}))] [FiberFunctor FU]
      (h : ContinuousMonoidHom (Aut FU) (Aut FX))
      (h_id : CatCommSq (finiteEtaleBaseChange U.ι) (functorToAction FX)
        (functorToAction FU) (Action.res FintypeCat h.toMonoidHom))
      (FUsh : ∀ i, FiniteEtale (PuncturedSpectrum.scheme (Ash i)) ⥤ FintypeCat.{w})
      [∀ i, GaloisCategory (FiniteEtale (PuncturedSpectrum.scheme (Ash i)))]
      [∀ i, FiberFunctor (FUsh i)]
      (hUsh : ∀ i, ContinuousMonoidHom (Aut (FUsh i)) (Aut FU))
      (hUsh_id : ∀ i,
        CatCommSq
          (finiteEtaleBaseChange
            (AlgebraicGeometry.Scheme.PuncturedStrictHenselization.map x hx U hUeq Ash i))
          (functorToAction FU) (functorToAction (FUsh i))
          (Action.res FintypeCat (hUsh i).toMonoidHom)),
      MonoidHom.ker h.toMonoidHom =
        (Subgroup.topologicalClosure
          (Subgroup.normalClosure
            (Set.iUnion fun i => Set.range (hUsh i).toMonoidHom))))
