module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Exact
import StacksCheckRecall

@[expose] public section

/- Lemma 20.10.1 (Tag 01EJ): the exactness statement is owned by the reusable ringed-site
presheaf-module Cech API. The chapter entry is a recall block, so later chapters import the
owner directly instead of depending on this file. -/

open CategoryTheory
open SheafOfModules.RingedSite

@[stacks 01EJ] #check @sectionsOnOverAdditive
@[stacks 01EJ] #check @sectionsOnOver_exact
@[stacks 01EJ] #check @cechComplexAdditive
@[stacks 01EJ] #check @cechComplex_exact
