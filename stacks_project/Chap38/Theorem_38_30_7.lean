module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Blowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Theorem 38.30.7: a finite-type quasicoherent module that is finitely presented and flat
over a quasi-compact open admits an admissible blowup whose strict transform is finitely
presented and flat over the new base. -/
@[stacks 0815] #check
  (@AlgebraicGeometry.Scheme.Modules.exists_isAdmissibleBlowup_flattening :
    {S X : Scheme.{u}} → [CompactSpace S] → [QuasiSeparatedSpace S] → [CompactSpace X] →
    (f : X ⟶ S) → [LocallyOfFinitePresentation f] →
    (ℱ : X.Modules) → [ℱ.IsQuasicoherent] → [ℱ.IsFiniteType] →
    (U : S.Opens) → [QuasiCompact U.ι] →
    [(ℱ.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation] →
    (h_flat : flatOver (ℱ.restrict ((f ⁻¹ᵁ U).ι)) (f ∣_ U)) →
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        let ℱ' := strictTransformModule b (I.comap b) f ℱ
        ℱ'.IsFinitePresentation ∧ flatOver ℱ' (pullback.snd f b))

end AlgebraicGeometry.Scheme.Modules
