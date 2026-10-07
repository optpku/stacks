module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.CommonRefinement
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Composition
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Extension
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Composition
import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 38.30.1 (1): a finite sequence of admissible blowups may be replaced by one
admissible blowup by iterating binary composition; the direct scheme and module strict
transforms are canonically isomorphic to the corresponding iterated strict transforms. -/
@[stacks 080Y] #check
  (AlgebraicGeometry.IsAdmissibleBlowup.comp :
    ∀ {X X' X'' : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      (U : X.Opens) (hU : AlgebraicGeometry.QuasiCompact U.ι)
      (b : X' ⟶ X) (hb : AlgebraicGeometry.IsAdmissibleBlowup U b)
      (b' : X'' ⟶ X') (hb' : AlgebraicGeometry.IsAdmissibleBlowup (b ⁻¹ᵁ U) b'),
      AlgebraicGeometry.IsAdmissibleBlowup U (b' ≫ b))

#check
  (AlgebraicGeometry.IsBlowup.exists_center_comp :
    ∀ {X X' X'' : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      (Z : X.IdealSheafData)
      (hZfp : AlgebraicGeometry.LocallyOfFinitePresentation Z.subschemeι)
      (b : X' ⟶ X) [AlgebraicGeometry.IsBlowup b Z]
      (Z' : X'.IdealSheafData)
      (hZ'fp : AlgebraicGeometry.LocallyOfFinitePresentation Z'.subschemeι)
      (b' : X'' ⟶ X') [AlgebraicGeometry.IsBlowup b' Z'],
      ∃ Y : {Y : X.IdealSheafData //
          AlgebraicGeometry.LocallyOfFinitePresentation Y.subschemeι},
        ((Y : X.IdealSheafData).support : Set X) =
            (Z.support : Set X) ∪ b.base '' (Z'.support : Set X') ∧
          AlgebraicGeometry.IsBlowup (b' ≫ b) (Y : X.IdealSheafData))

#check
  (AlgebraicGeometry.Scheme.Modules.strictTransformModule_isomorphic_pushforward_iteratedStrictTransform :
    ∀ {S S' S'' X : AlgebraicGeometry.Scheme.{u}} (Z : S.IdealSheafData)
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b Z]
      (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [AlgebraicGeometry.IsBlowup b' Z']
      (Y : S.IdealSheafData),
      (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S') →
      ∀ [AlgebraicGeometry.IsBlowup (b' ≫ b) Y]
        (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        CategoryTheory.IsIsomorphic
          (AlgebraicGeometry.strictTransformModule (b' ≫ b) (Y.comap (b' ≫ b)) f ℱ)
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (CategoryTheory.Limits.pullbackLeftPullbackSndIso f b b').hom).obj
            (AlgebraicGeometry.strictTransformModule b' (Z'.comap b')
              (CategoryTheory.Limits.pullback.snd f b)
              (AlgebraicGeometry.strictTransformModule b (Z.comap b) f ℱ))))

#check
  (AlgebraicGeometry.strictTransform_isomorphic_iteratedStrictTransform :
    ∀ {S S' S'' X : AlgebraicGeometry.Scheme.{u}} (Z : S.IdealSheafData)
      (b : S' ⟶ S) [AlgebraicGeometry.IsBlowup b Z]
      (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [AlgebraicGeometry.IsBlowup b' Z']
      (Y : S.IdealSheafData),
      (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S') →
      ∀ [AlgebraicGeometry.IsBlowup (b' ≫ b) Y] (f : X ⟶ S),
        CategoryTheory.IsIsomorphic
          (AlgebraicGeometry.strictTransform (b' ≫ b) (Y.comap (b' ≫ b)) f)
          (AlgebraicGeometry.strictTransform b' (Z'.comap b')
            (AlgebraicGeometry.strictTransformSnd b (Z.comap b) f)))

#check
  (AlgebraicGeometry.strictTransformSnd :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (b : S' ⟶ S)
      (E : S'.IdealSheafData) (f : X ⟶ S),
      AlgebraicGeometry.strictTransform b E f ⟶ S')

#check
  (AlgebraicGeometry.strictTransformModule_isQuasicoherent :
    ∀ {S S' X : AlgebraicGeometry.Scheme.{u}} (b : S' ⟶ S)
      (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules)
      [AlgebraicGeometry.IsEffectiveCartierDivisor E.subschemeι] [ℱ.IsQuasicoherent],
      (AlgebraicGeometry.strictTransformModule b E f ℱ).IsQuasicoherent)

/- Remark 38.30.1 (2): a quasi-compact open of a quasi-compact quasi-separated scheme has
complement given by the support of finite-type ideal-sheaf data. Blowing up this ideal produces
an effective Cartier exceptional divisor whose open complement is scheme-theoretically dense. -/
@[stacks 080Y] #check
  (AlgebraicGeometry.Scheme.retrocompactOpen_tfae :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U : X.Opens),
      List.TFAE [
        IsRetrocompact (U : Set X),
        IsCompact (U : Set X),
        ∃ s : Set X.affineOpens, s.Finite ∧ U = ⨆ V ∈ s, (V : X.Opens),
        ∃ I : X.IdealSheafData, I.IsFiniteType ∧ I.support = U.compl
      ])

#check
  (AlgebraicGeometry.Blowup.exceptionalDivisor :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I), π.scheme.IdealSheafData)

#check
  (AlgebraicGeometry.IsBlowup.instIsEffectiveCartierDivisor :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData} {f : X' ⟶ X}
      [AlgebraicGeometry.IsBlowup f I],
      AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap f).subschemeι)

#check
  (AlgebraicGeometry.Scheme.IdealSheafData.support_comap :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y),
      (I.comap f).support = I.support.preimage f.continuous)

#check
  (AlgebraicGeometry.IsEffectiveCartierDivisor.schemeTheoreticallyDense_closedImmersionComplement :
    ∀ {S D : AlgebraicGeometry.Scheme.{u}} (i : D ⟶ S)
      [AlgebraicGeometry.IsEffectiveCartierDivisor i],
      AlgebraicGeometry.schemeTheoreticallyDense
        (AlgebraicGeometry.closedImmersionComplement i))

/- Remark 38.30.1 (3): a local admissible blowup over a quasi-compact open extends to the
ambient quasi-compact quasi-separated scheme. Extension followed by a finite common refinement
reduces a restriction-stable strict-transform problem that is local for finite quasi-compact
open covers to the corresponding local problems. -/
@[stacks 080Y] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter :
    ∀ {X V' : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U V : X.Opens) (hU : AlgebraicGeometry.QuasiCompact U.ι)
      (hV : AlgebraicGeometry.QuasiCompact V.ι) (b : V' ⟶ V.toScheme),
      AlgebraicGeometry.IsAdmissibleBlowup (V.ι ⁻¹ᵁ U) b →
        ∃ (X' : AlgebraicGeometry.Scheme.{u}) (π : X' ⟶ X),
          AlgebraicGeometry.IsAdmissibleBlowup U π ∧
            Nonempty (Over.mk (π ∣_ V) ≅ Over.mk b))

#check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_common_refinement :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U : X.Opens) (hU : AlgebraicGeometry.QuasiCompact U.ι)
      {n : ℕ} (Xi : Fin n → AlgebraicGeometry.Scheme.{u})
      (bi : ∀ i : Fin n, Xi i ⟶ X)
      (hbi : ∀ i : Fin n, AlgebraicGeometry.IsAdmissibleBlowup U (bi i)),
      ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
        AlgebraicGeometry.IsAdmissibleBlowup U b ∧
          ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
            c ≫ bi i = b ∧
              AlgebraicGeometry.IsAdmissibleBlowup (bi i ⁻¹ᵁ U) c)
