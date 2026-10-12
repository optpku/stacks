/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
import StacksCheckRecall

@[expose] public section

/-!
# Definition 29.7.1

The scheme-theoretic closure and scheme-theoretic density API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure`.
-/

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}} (U V : X.Opens)

/- Definition 29.7.1: The scheme-theoretic closure of an open subscheme is the
scheme-theoretic image of its inclusion, and scheme-theoretic density means
that every relative closure has bottom defining ideal. -/
@[stacks 01RB] #check
  (AlgebraicGeometry.schemeTheoreticClosure_eq_image U :
    AlgebraicGeometry.schemeTheoreticClosure U =
      AlgebraicGeometry.Scheme.Hom.image U.ι)

#check
  (AlgebraicGeometry.Scheme.Hom.ker :
    (X ⟶ Y) → Y.IdealSheafData)

#check
  (AlgebraicGeometry.Scheme.Hom.image :
    (X ⟶ Y) → AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.IsSchemeTheoreticallyDominant :
    (X ⟶ Y) → Prop)

#check
  (AlgebraicGeometry.schemeTheoreticClosureIdeal U : X.IdealSheafData)

#check
  (AlgebraicGeometry.schemeTheoreticClosureIdeal_eq_ker U :
    AlgebraicGeometry.schemeTheoreticClosureIdeal U = U.ι.ker)

#check
  (AlgebraicGeometry.schemeTheoreticClosure U : AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.schemeTheoreticClosureι U :
    AlgebraicGeometry.schemeTheoreticClosure U ⟶ X)

#check
  (AlgebraicGeometry.schemeTheoreticClosureι_eq_imageι U :
    AlgebraicGeometry.schemeTheoreticClosureι U =
      AlgebraicGeometry.Scheme.Hom.imageι U.ι)

#check
  (AlgebraicGeometry.schemeTheoreticClosureInIdeal U V : V.toScheme.IdealSheafData)

#check
  (AlgebraicGeometry.schemeTheoreticClosureInIdeal_eq_ker U V :
    AlgebraicGeometry.schemeTheoreticClosureInIdeal U V =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).ker)

#check
  (AlgebraicGeometry.schemeTheoreticClosureIn U V : AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.schemeTheoreticClosureInι U V :
    AlgebraicGeometry.schemeTheoreticClosureIn U V ⟶ V)

#check
  (AlgebraicGeometry.schemeTheoreticClosureIn_eq_image U V :
    AlgebraicGeometry.schemeTheoreticClosureIn U V =
      AlgebraicGeometry.Scheme.Hom.image
        (X.homOfLE (inf_le_right : U ⊓ V ≤ V)))

#check
  (AlgebraicGeometry.schemeTheoreticClosureInι_eq_imageι U V :
    AlgebraicGeometry.schemeTheoreticClosureInι U V =
      AlgebraicGeometry.Scheme.Hom.imageι
        (X.homOfLE (inf_le_right : U ⊓ V ≤ V)))

#check
  (AlgebraicGeometry.schemeTheoreticallyDense U : Prop)

#check
  (AlgebraicGeometry.schemeTheoreticallyDense_iff U :
    AlgebraicGeometry.schemeTheoreticallyDense U ↔
      ∀ V : X.Opens,
        AlgebraicGeometry.schemeTheoreticClosureInIdeal U V = ⊥)

#check
  (AlgebraicGeometry.schemeTheoreticallyDense_iff_forall_isSchemeTheoreticallyDominant U :
    AlgebraicGeometry.schemeTheoreticallyDense U ↔
      ∀ V : X.Opens,
        AlgebraicGeometry.IsSchemeTheoreticallyDominant
          (X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
