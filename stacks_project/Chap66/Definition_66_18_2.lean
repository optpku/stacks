module

public import stacks_project.Chap66.Lemma_66_18_3_Site
import StacksCheckRecall

@[expose] public section

/- Definition 66.18.2: let `S` be a scheme and let `X` be an algebraic space over `S`.
The site `X_spaces,étale` of `X` is the Grothendieck topology `spacesEtaleTopology X` on
the category `spacesEtaleSite X` of algebraic spaces étale over `X` (objects are étale
morphisms `φ : U ⟶ X` of algebraic spaces over `S` with `Etale φ`, morphisms
`χ : U ⟶ U'` over `X` satisfy `χ ≫ φ' = φ`), whose covering families are those jointly
surjective on points, i.e. `|U| = ⋃ i, Points.map χ_i '' |U_i|`. Coverings are chosen as
a `Small` set of such families, containing at least the coverings of `smallEtaleSite X`
via `smallEtaleInclusion`, as in Sets Lemma 3.11.1, generating `spacesEtalePrecoverage`
and then `spacesEtaleTopology`. -/
@[stacks 03G0] #check AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology
