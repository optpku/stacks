module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.LisseStratification
import StacksCheckRecall

/-!
# Lemma 61.28.2

On a Noetherian scheme, a constructible `Λ`-sheaf on the pro-étale site
admits a finite locally closed partition on which it is lisse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.28.2: a constructible sheaf on a Noetherian scheme admits a finite
locally closed partition on which its restriction is lisse. -/
@[stacks 09BU] #check (AlgebraicGeometry.Scheme.ProEt.exists_locallyClosedPartition_isLisse :
  ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
    [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
    [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (P : Z.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
      (baseChange f).op.HasLeftKanExtension P]
    [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [∀ {Y : Scheme.{u}} (U : Y.ProEt),
      HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]
    (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ)) [IsNoetherian X]
    [IsConstructibleLambdaSheaf I F],
    ∃ (Q : LocallyClosedPartition X), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        let T : LocallyCloseds X :=
          ⟨(s : Set X), Q.locallyClosed_of_mem s.property⟩
        IsLisse I (moduleRestrict (LocallyClosedReduction.ι T) F))
