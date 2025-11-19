import java.util.concurrent.locks.*;

/*@
  predicate node (Node h; int v, Node left, Node right) =
    h.val |-> v &*&
    h.left |-> left &*&
    h.right |-> right;

  predicate tree (Node h;) = true;

  predicate non_empty_tree (Node h;) = true;

  predicate heap (Heap h;) = true;

  predicate non_empty_heap (Heap h;) = true;

  predicate pairing_heap (PairingHeap h;) = true;

  predicate non_empty_pairing_heap (PairingHeap h;) = true;

@*/

class Node {
    private int val;
    private Node left, right;

    public Node (int val)
    //@ requires true;
    //@ ensures true;
    {
        this.val = val;
        this.left = null;
        this.right = null;
    }

    public Node (Node left, int val, Node right)
    //@ requires true;
    //@ ensures true;
    {
        this.val = val;
        this.left = left;
        this.right = right;
    }

    public int getVal ()
    //@ requires true;
    //@ ensures true;
    {
        return this.val;
    }

    public Node getLeft ()
    //@ requires true;
    //@ ensures true;
    {
        return this.left;
    }

    public Node getRight ()
    //@ requires true;
    //@ ensures true;
    {
        return this.right;
    }

    public void setLeft (Node left)
    //@ requires true;
    //@ ensures true;
    {
        this.left = left;
    }

    public void setRight (Node right)
    //@ requires true;
    //@ ensures true;
    {
        this.right = right;
    }
}

class Heap {
    private int val;
    private Node tree;

    public Heap (int val)
    //@ requires true;
    //@ ensures true;
    {
        this.val = val;
        this.tree = null;
    }

    public Heap (int val, Node t)
    //@ requires true;
    //@ ensures true;
    {
        this.val = val;
        this.tree = t;
    }

    public static boolean isEmpty (Heap h)
    //@ requires true;
    //@ ensures true;
    {
        return h == null;
    }

    public static int getMin (Heap h)
    //@ requires true;
    //@ ensures true;
    {
        return h.val;
    }

    private static Heap merge (Heap h1, Heap h2)
    //@ requires true;
    //@ ensures true;
    {
        if (h1 == null) {
            return h2;
        }
        if (h2 == null) {
            return h1;
        }

        if (h1.val <= h2.val) {
            Node t = new Node(h2.tree, h2.val, h1.tree);
            Heap r = new Heap(h1.val, t);
            return r;
        }
        else {
            Node t = new Node(h1.tree, h1.val, h2.tree);
            Heap r = new Heap(h2.val, t);
            return r;
        }
    }

    public static Heap add (int v, Heap h)
    //@ requires true;
    //@ ensures true;
    {
        Heap tmp = new Heap(v);

        return merge(h, tmp);
    }

    private static Heap mergePairs (Node t)
    //@ requires true;
    //@ ensures true;
    {
        if (t == null) return null;
        if (t.getRight() == null) return new Heap(t.getVal(), t.getLeft());

        Node right = t.getRight();
        Node rightRight = right.getRight();

        Heap r = mergePairs(rightRight);

        Heap h1 = new Heap(t.getVal(), t.getLeft());
        Heap h2 = new Heap(right.getVal(), right.getLeft());

        Heap h = merge(h1, h2);

        return merge(h, r);
    }

    public static Heap removeMin (Heap h)
    //@ requires true;
    //@ ensures true;
    {
        Heap r = mergePairs(h.tree);

        return r;
    }
}

public class PairingHeap {
    Heap head;

    public PairingHeap ()
    //@ requires true;
    //@ ensures true;
    {
        head = null;
    }

    public PairingHeap (Heap head)
    //@ requires true;
    //@ ensures true;
    {
        this.head = head;
    }

    public PairingHeap (int v)
    //@ requires true;
    //@ ensures true;
    {
        this.head = new Heap(v);
    }

    public boolean isEmpty ()
    //@ requires true;
    //@ ensures true;
    {
        return this.head == null;
    }

    public int getMin ()
    //@ requires true;
    //@ ensures true;
    {
        return Heap.getMin(this.head);
    }

    public void add (int v)
    //@ requires true;
    //@ ensures true;
    {
        Heap tmp = Heap.add(v, head);
        head = tmp;
    }

    public void removeMin ()
    //@ requires true;
    //@ ensures true;
    {
        Heap tmp = Heap.removeMin(head);
        head = tmp;
    }
}
