/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

section

variable {R : Type u} [CommRing R] [StrictHenselianLocalRing R]

/- Lemma 59.55.1 (1): for a strictly henselian local ring, global sections on
the small etale site of its spectrum are an exact functor on abelian sheaves. -/
@[stacks 03QO] #check
  (AlgebraicGeometry.Scheme.Etale.strictHenselianGlobalSectionsExact (R := R) :
    exactFunctor
      (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u})
      AddCommGrpCat.{u}
      (siteAbelianSectionsFunctor
        (Scheme.smallEtaleTopology (Spec (.of R)))
        (MorphismProperty.Over.mk _ (𝟙 (Spec (.of R))) inferInstance)))

end

section

variable {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
variable (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) (Type u))

/- Lemma 59.55.1 (2): for a sheaf of sets on the small etale site of the
strictly henselian local scheme `Spec R`, global sections are the stalk at its
closed geometric point. -/
@[stacks 03QO] #check
  (AlgebraicGeometry.Scheme.Etale.strictHenselianGlobalSectionsEqClosedPointStalk
    (R := R) F :
    IsIsomorphic
      (F.obj.obj (op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of R))) inferInstance)))
      (((Scheme.pointSmallEtale
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).sheafFiber).obj F))

end

section

variable {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
variable [HasSheafify (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u})]
variable (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{u})

/- Lemma 59.55.1 (3): positive-degree etale cohomology of every abelian sheaf
on the spectrum of a strictly henselian local ring vanishes. -/
@[stacks 03QO] #check
  (AlgebraicGeometry.Scheme.Etale.strictHenselianPositiveCohomologyIsZero
    (R := R) F :
    ∀ p : ℕ, 0 < p →
      IsZero ((Sheaf.functorH (Scheme.smallEtaleTopology (Spec (.of R))) p).obj F))

end

end
