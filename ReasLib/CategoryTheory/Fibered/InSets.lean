/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
public import ReasLib.CategoryTheory.Fibered.InSets.Forgetful
public import ReasLib.CategoryTheory.Fibered.InSets.LocalDiscreteness
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.Sets.TwoFibreProduct

/-!
# Categories fibred in sets

Compatibility aggregate for the bicategory owner, morphism and forgetful computation APIs,
local discreteness, canonical slice, neutral full-subbicategory equivalence lift, and neutral
two-fibre products. New direct users should import the narrow leaf owning the construction.
-/
