# Lists

### Write Coq code for any of the following. You may want to write definitions or prior theorems / lemmas for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the Lists module.

- `Theorem snd_fst_is_swap : ∀ (p : natprod), (snd p, fst p) = swap_pair p.`
- `Theorem fst_swap_is_snd : ∀ (p : natprod), fst (swap_pair p) = snd p.`
- `Fixpoint nonzeros (l:natlist) : natlist`
- `Fixpoint oddmembers (l:natlist) : natlist`
- `Theorem app_nil_r : ∀ l : natlist,  l ++ [ ] = l.`
- `Theorem rev_app_distr: ∀ l1 l2 : natlist,  rev (l1 ++ l2) = rev l2 ++ rev l1.`