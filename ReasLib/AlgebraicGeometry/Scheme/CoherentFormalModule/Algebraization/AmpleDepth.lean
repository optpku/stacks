/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.StalkLimit
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.Topology.KrullDimension.Local
public import Mathlib.Order.WithBotTop

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- For a proper scheme `P` over a field, an ample invertible module `L` with
section `s`, and a coherent formal module `F` along the zero scheme `Q = Z(s)`,
the completed-stalk depth, quotient-dimension, and closure-dimension bound at
every `q ∈ Q` and every prime outside the completed ideal implies that `F` is
the completion of a coherent module on `P`. -/
theorem isCompletion_of_depth_dimension
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [IsNoetherian P.left] (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections)
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_depth : ∀ q : P.left, q ∈ Set.range (zeroSchemeι L s) →
      let X := P.left
      let A_q := X.presheaf.stalk q
      let I_q : Ideal A_q :=
        RingedSpace.idealSheafStalkIdeal (zeroIdealSheaf L s).toSubobject q
      let M_q : ModuleCat A_q :=
        limit (F.obj ⋙ (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
          X.toRingedSpace.stalkModuleFunctor q)
      let Ahat_q := AdicCompletion I_q A_q
      let Mhat_q : ModuleCat Ahat_q :=
        @ModuleCat.of Ahat_q _ M_q _
          (@IsAdicComplete.completedModule A_q _ I_q M_q _ _
            (stalkLimit_isAdicComplete_of_coherentFormalModule
              (zeroIdealSheaf L s) F q))
      let Ihat_q : Ideal Ahat_q := I_q.map (algebraMap A_q Ahat_q)
      ∀ p : PrimeSpectrum Ahat_q,
        p ∉ PrimeSpectrum.zeroLocus (Ihat_q : Set Ahat_q) →
          (2 : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal Mhat_q)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (Ahat_q ⧸ p.asIdeal)) +
              WithBot.map (WithTop.map Int.ofNat)
                (topologicalKrullDim (closure ({q} : Set X)))) :
    (CoherentCompletion.functor (zeroIdealSheaf L s)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
