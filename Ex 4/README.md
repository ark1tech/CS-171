# Polymorphism and Higher Order Types
### Write Coq code for any of the following. You may want to write definitions or prior theorems / lemmas for data types (i.e. bool / nat) in your code before writing code for these. For more details, you may check the Poly module.

- `Theorem app_nil_r : ∀ (X:Type), ∀ l:list X, l ++ [ ] = l.`
- `Theorem rev_involutive : ∀ X : Type, ∀ l : list X, rev (rev l) = l.`
- `Example test_filter_even_gt7_1 :  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].`
- `Theorem map_rev : ∀ (X Y : Type) (f : X → Y) (l : list X), map f (rev l) = rev (map f l).`