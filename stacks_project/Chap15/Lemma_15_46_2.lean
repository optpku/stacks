/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PBasis.Existence
public import ReasLib.FieldTheory.PBasis.Kaehler
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.46.2

The differential criteria and existence theorems for `p`-bases are owned directly by
`FieldExtension.PBasis`.

@stack 07P2
-/

/- Lemma 15.46.2, equivalence (1)--(2): differential criterion for `p`-independence. -/
@[stacks 07P2 "Lemma 15.46.2, equivalence (1)-(2): differential criterion"]
#check @FieldExtension.PBasis.isIndependent_iff_differentials

/- Lemma 15.46.2, extension conclusion: every `p`-independent family extends to a `p`-basis. -/
@[stacks 07P2 "Lemma 15.46.2, extension to a p-basis"]
#check @FieldExtension.PBasis.exists_extension

/- Lemma 15.46.2, existence conclusion: every field extension in the source setting has a
`p`-basis. -/
@[stacks 07P2 "Lemma 15.46.2, existence of a p-basis"]
#check @FieldExtension.PBasis.exists_basis

/- Lemma 15.46.2, equivalence (a)--(b): differential basis criterion for a `p`-basis. -/
@[stacks 07P2 "Lemma 15.46.2, equivalence (a)-(b): differential basis criterion"]
#check @FieldExtension.PBasis.isBasis_iff_differentials

#check @FieldExtension.PBasis.differentials

end
