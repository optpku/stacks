module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocalAtTarget
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 37.66.2: for a scheme morphism `f : X ⟶ Y`, ind-quasi-affineness is
equivalent to the compact-open quasi-affineness criterion over every affine
target open, over some quasi-compact and quasi-separated open cover, or over
every quasi-compact and quasi-separated target open. -/
@[stacks 0F1U] #check
  (AlgebraicGeometry.indQuasiAffineHom_tfae :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      List.TFAE
        [ AlgebraicGeometry.IndQuasiAffineHom f
        , ∀ V : Y.affineOpens, (f ∣_ V).IsQuasiAffineOnCompactOpens
        , ∃ (J : Type u) (V : J → Y.Opens), iSup V = ⊤ ∧
            ∀ j : J, IsCompact (V j : Set Y) ∧
              QuasiSeparatedSpace (V j).toScheme ∧
                (f ∣_ (V j)).IsQuasiAffineOnCompactOpens
        , ∀ V : Y.Opens, IsCompact (V : Set Y) →
            QuasiSeparatedSpace V.toScheme →
              (f ∣_ V).IsQuasiAffineOnCompactOpens
        ])

/- Ind-quasi-affineness of scheme morphisms is Zariski local on the target. -/
#check (AlgebraicGeometry.IndQuasiAffineHom.isZariskiLocalAtTarget :
  AlgebraicGeometry.IsZariskiLocalAtTarget
    (@AlgebraicGeometry.IndQuasiAffineHom :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}))
