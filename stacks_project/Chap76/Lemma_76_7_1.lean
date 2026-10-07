module

public import stacks_project.Chap76.Lemma_76_7_1_Instances
public import stacks_project.Chap76.Lemma_76_7_1_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.Etale.Small
open Scheme.Etale.Small
open scoped AlgebraicGeometry RingedSite.Hom

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Lemma 76.7.1 (1): for a morphism of schemes `f : X ⟶ Y`, the sheaf on `X.Etale`
associated to the quasi-coherent module `Ω[f.toShHom]` is canonically isomorphic
to the site-theoretic relative differentials `Ω[commRingedHom f]` of the small
étale ringed morphism `f_small`. -/
@[stacks 04CS]
#check (associatedModuleIso f :
  RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) ≅
    StandardSmall.comm .etale X (Ω[f.toShHom]))

/- Lemma 76.7.1 (2): the comparison intertwines the site-theoretic universal
derivation with the associated étale derivation `d^a`. -/
@[stacks 04CS]
#check (associatedModuleIso_comp_universalDerivation f :
  (d[commRingedHom f]).postcomp (associatedModuleIso f).hom.val =
    associatedUniversalDerivation f)
