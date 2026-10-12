/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_19_0_2_PrincipalParts»
public import stacks_project.Chap92.«92_19_0_2_Triangle»
import StacksCheckRecall

open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

/- 92.19.0.2: on a site, for a homomorphism of ring sheaves φ : A ⟶ B and a B-module sheaf F,
the degreewise first principal-parts extensions of F along the standard resolution P_• ⟶ B
assemble to a short exact sequence of simplicial P_•-modules. Applying
Lπ_! : D(P_•) ⟶ D(B) yields the distinguished triangle
L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F)) ⟶ F ⟶ (L(φ) ⊗^L F)⟦1⟧ in D(B). -/
@[stacks 09DH]
#check atiyahTriangle_distinguished

#check atiyahTriangle
#check atiyahTriangle_ofSES
#check atiyahLowerShriek
#check tensorModule
#check derivedPrincipalParts
#check tensorToPrincipalParts
#check principalPartsToModule
#check connectingMap
#check tensorIso
#check moduleIso
#check tensorIso_hom
#check moduleIso_hom
#check atiyahTriangle_obj₁
#check atiyahTriangle_obj₂
#check atiyahTriangle_obj₃
#check atiyahTriangle_mor₁
#check atiyahTriangle_mor₂
#check atiyahTriangle_mor₃
#check atiyahSequence
#check atiyahSequence_shortExact
#check principalPartsModule
#check cotangentModule
#check restrictedModule
#check degreeSequence_eq_atiyahExtension
#check augmentation
