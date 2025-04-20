theory append_assoc [simp]
     imports Main "../../FIFO_queue"
begin


lemma append_assoc [simp]: "xs @ (ys @ zs) = (xs @ ys) @ zs" nitpick sorry




end