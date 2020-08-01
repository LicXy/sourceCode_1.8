/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package java.util;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Hash table based implementation of the <tt>Map</tt> interface.  This
 * implementation provides all of the optional map operations, and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  (The <tt>HashMap</tt>
 * class is roughly equivalent to <tt>Hashtable</tt>, except that it is
 * unsynchronized and permits nulls.)  This class makes no guarantees as to
 * the order of the map; in particular, it does not guarantee that the order
 * will remain constant over time.
 *
 * <p>This implementation provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the hash function
 * disperses the elements properly among the buckets.  Iteration over
 * collection views requires time proportional to the "capacity" of the
 * <tt>HashMap</tt> instance (the number of buckets) plus its size (the number
 * of key-value mappings).  Thus, it's very important not to set the initial
 * capacity too high (or the load factor too low) if iteration performance is
 * important.
 *
 * <p>An instance of <tt>HashMap</tt> has two parameters that affect its
 * performance: <i>initial capacity</i> and <i>load factor</i>.  The
 * <i>capacity</i> is the number of buckets in the hash table, and the initial
 * capacity is simply the capacity at the time the hash table is created.  The
 * <i>load factor</i> is a measure of how full the hash table is allowed to
 * get before its capacity is automatically increased.  When the number of
 * entries in the hash table exceeds the product of the load factor and the
 * current capacity, the hash table is <i>rehashed</i> (that is, internal data
 * structures are rebuilt) so that the hash table has approximately twice the
 * number of buckets.
 *
 * <p>As a general rule, the default load factor (.75) offers a good
 * tradeoff between time and space costs.  Higher values decrease the
 * space overhead but increase the lookup cost (reflected in most of
 * the operations of the <tt>HashMap</tt> class, including
 * <tt>get</tt> and <tt>put</tt>).  The expected number of entries in
 * the map and its load factor should be taken into account when
 * setting its initial capacity, so as to minimize the number of
 * rehash operations.  If the initial capacity is greater than the
 * maximum number of entries divided by the load factor, no rehash
 * operations will ever occur.
 *
 * <p>If many mappings are to be stored in a <tt>HashMap</tt>
 * instance, creating it with a sufficiently large capacity will allow
 * the mappings to be stored more efficiently than letting it perform
 * automatic rehashing as needed to grow the table.  Note that using
 * many keys with the same {@code hashCode()} is a sure way to slow
 * down performance of any hash table. To ameliorate impact, when keys
 * are {@link Comparable}, this class may use comparison order among
 * keys to help break ties.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access a hash map concurrently, and at least one of
 * the threads modifies the map structurally, it <i>must</i> be
 * synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 *
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new HashMap(...));</pre>
 *
 * <p>The iterators returned by all of this class's "collection view methods"
 * are <i>fail-fast</i>: if the map is structurally modified at any time after
 * the iterator is created, in any way except through the iterator's own
 * <tt>remove</tt> method, the iterator will throw a
 * {@link ConcurrentModificationException}.  Thus, in the face of concurrent
 * modification, the iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the
 * future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw <tt>ConcurrentModificationException</tt> on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>the fail-fast behavior of iterators
 * should be used only to detect bugs.</i>
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 *
 * @author  Doug Lea
 * @author  Josh Bloch
 * @author  Arthur van Hoff
 * @author  Neal Gafter
 * @see     Object#hashCode()
 * @see     Collection
 * @see     Map
 * @see     TreeMap
 * @see     Hashtable
 * @since   1.2
 */
public class HashMap<K,V> extends AbstractMap<K,V>
    implements Map<K,V>, Cloneable, Serializable {

    private static final long serialVersionUID = 362498820763181265L;

    /*
     * Implementation notes.
     *
     * This map usually acts as a binned (bucketed) hash table, but
     * when bins get too large, they are transformed into bins of
     * TreeNodes, each structured similarly to those in
     * java.util.TreeMap. Most methods try to use normal bins, but
     * relay to TreeNode methods when applicable (simply by checking
     * instanceof a node).  Bins of TreeNodes may be traversed and
     * used like any others, but additionally support faster lookup
     * when overpopulated. However, since the vast majority of bins in
     * normal use are not overpopulated, checking for existence of
     * tree bins may be delayed in the course of table methods.
     *
     * Tree bins (i.e., bins whose elements are all TreeNodes) are
     * ordered primarily by hashCode, but in the case of ties, if two
     * elements are of the same "class C implements Comparable<C>",
     * type then their compareTo method is used for ordering. (We
     * conservatively check generic types via reflection to validate
     * this -- see method comparableClassFor).  The added complexity
     * of tree bins is worthwhile in providing worst-case O(log n)
     * operations when keys either have distinct hashes or are
     * orderable, Thus, performance degrades gracefully under
     * accidental or malicious usages in which hashCode() methods
     * return values that are poorly distributed, as well as those in
     * which many keys share a hashCode, so long as they are also
     * Comparable. (If neither of these apply, we may waste about a
     * factor of two in time and space compared to taking no
     * precautions. But the only known cases stem from poor user
     * programming practices that are already so slow that this makes
     * little difference.)
     *
     * Because TreeNodes are about twice the size of regular nodes, we
     * use them only when bins contain enough nodes to warrant use
     * (see TREEIFY_THRESHOLD). And when they become too small (due to
     * removal or resizing) they are converted back to plain bins.  In
     * usages with well-distributed user hashCodes, tree bins are
     * rarely used.  Ideally, under random hashCodes, the frequency of
     * nodes in bins follows a Poisson distribution
     * (http://en.wikipedia.org/wiki/Poisson_distribution) with a
     * parameter of about 0.5 on average for the default resizing
     * threshold of 0.75, although with a large variance because of
     * resizing granularity. Ignoring variance, the expected
     * occurrences of list size k are (exp(-0.5) * pow(0.5, k) /
     * factorial(k)). The first values are:
     *
     * 0:    0.60653066
     * 1:    0.30326533
     * 2:    0.07581633
     * 3:    0.01263606
     * 4:    0.00157952
     * 5:    0.00015795
     * 6:    0.00001316
     * 7:    0.00000094
     * 8:    0.00000006
     * more: less than 1 in ten million
     *
     * The root of a tree bin is normally its first node.  However,
     * sometimes (currently only upon Iterator.remove), the root might
     * be elsewhere, but can be recovered following parent links
     * (method TreeNode.root()).
     *
     * All applicable internal methods accept a hash code as an
     * argument (as normally supplied from a public method), allowing
     * them to call each other without recomputing user hashCodes.
     * Most internal methods also accept a "tab" argument, that is
     * normally the current table, but may be a new or old one when
     * resizing or converting.
     *
     * When bin lists are treeified, split, or untreeified, we keep
     * them in the same relative access/traversal order (i.e., field
     * Node.next) to better preserve locality, and to slightly
     * simplify handling of splits and traversals that invoke
     * iterator.remove. When using comparators on insertion, to keep a
     * total ordering (or as close as is required here) across
     * rebalancings, we compare classes and identityHashCodes as
     * tie-breakers.
     *
     * The use and transitions among plain vs tree modes is
     * complicated by the existence of subclass LinkedHashMap. See
     * below for hook methods defined to be invoked upon insertion,
     * removal and access that allow LinkedHashMap internals to
     * otherwise remain independent of these mechanics. (This also
     * requires that a map instance be passed to some utility methods
     * that may create new nodes.)
     *
     * The concurrent-programming-like SSA-based coding style helps
     * avoid aliasing errors amid all of the twisty pointer operations.
     */

    /**
     * The default initial capacity - MUST be a power of two.
     */
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<30.
     */
    static final int MAXIMUM_CAPACITY = 1 << 30;

    /**
     * The load factor used when none specified in constructor.
     */
    static final float DEFAULT_LOAD_FACTOR = 0.75f;

    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2 and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     *
     * 当链表长度达到8时, 将链表转为红黑树;
     *  注意:  HashMap每个slot可能存在值的几率是0.5, 即λ = 0.5
     *        泊松分布公式: exp(-0.5) * pow(0.5, k) / factorial(k)
     *        多个节点经过hash计算索引后, 在出现hash冲突, 在同一个桶内的概率符合泊松分布
     *        (注意:下面的数据模型是基于负载因子为0.75):
     *
     *   0:    0.60653066
     *   1:    0.30326533
     *   2:    0.07581633
     *   3:    0.01263606
     *   4:    0.00157952
     *   5:    0.00015795
     *   6:    0.00001316
     *   7:    0.00000094
     *   8:    0.00000006
     *   more: less than 1 in ten million
     *
     *   当8个节点出现hash冲突在同一个桶内的概率为0.00000006, 所以在链表长度超过8的时候【可能】转为红黑树,
     *   可见Hash表这样设计的本意是为了避免出现链表转为红黑树的情况
     *
     *   TREEIFY_THRESHOLD的设定是为了避免在出现链表转红黑树的情况, 但是另一方面需要防止在特定的数
     *   据规模中,出现HashMap退化为链表导致查询效率急剧下降的情况
     *
     */
    static final int TREEIFY_THRESHOLD = 8;

    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     *
     * 当红黑树中的节点数量小于6时,红黑树将转换为链表
     */
    static final int UNTREEIFY_THRESHOLD = 6;

    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * Should be at least 4 * TREEIFY_THRESHOLD to avoid conflicts
     * between resizing and treeification thresholds.
     *
     *  HashMap中链表长度超过8的时候【可能】转为红黑树
     * 当链表长度超过8时, 首先判断hash表的长度是否大于最小红黑树容量(也就是hash表中出现红黑树需要达到的最小容量)
     *  大于等于最小红黑树容量才会将链表转换为红黑树, 【如果小于, 则进行的是扩容操作, 而不是转换红黑树】
     */
    static final int MIN_TREEIFY_CAPACITY = 64;

    /**
     * Node节点,
     *    1.存储节点数据(key, value)
     *    2.存储key的hash值
     *    3.下一个节点的索引(用于链表模式下指向下一个节点, 单向链表)
     * 为什么使用单向链表?
     *    1. 节省内存, 仅存储下一个节点的地址即可
     *    2. 当出现hash值相同的key时, key会遍历该链表所有的节点, 判断是否存在相同的key,
     *    如果有, 则覆盖该节点. 如果查询至链表尾部, 仍然没有相同key,则就在该链表尾部新增节点
     */
    static class Node<K,V> implements Map.Entry<K,V> {
        final int hash;  //存储key的hash值, 用于计算该key在Hash表中的索引位置
        final K key;     //key值, 不允许修改, 覆盖 (注:如果出现相同key,则直接覆盖value即可)
        V value;
        Node<K,V> next;  //下一个节点的地址

        Node(int hash, K key, V value, Node<K,V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey()        { return key; }
        public final V getValue()      { return value; }
        public final String toString() { return key + "=" + value; }

        public final int hashCode() {
            //key的hash值与value的hash值的异或运算
            //异或运算: 0^0=0,0^1=1,1^0=1,1^1=0; 即: 参加运算的两个对象，如果两个相应位为“异”（值不同），则该位结果为1，否则为0
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;  //在更新value后, 会返回旧的value值
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>)o;
                //key与value都需要根据各自定义的equals方法认定为相同
                if (Objects.equals(key, e.getKey()) &&
                    Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }

    /* ---------------- Static utilities -------------- */

    /**
     * Computes key.hashCode() and spreads (XORs) higher bits of hash
     * to lower.  Because the table uses power-of-two masking, sets of
     * hashes that vary only in bits above the current mask will
     * always collide. (Among known examples are sets of Float keys
     * holding consecutive whole numbers in small tables.)  So we
     * apply a transform that spreads the impact of higher bits
     * downward. There is a tradeoff between speed, utility, and
     * quality of bit-spreading. Because many common sets of hashes
     * are already reasonably distributed (so don't benefit from
     * spreading), and because we use trees to handle large sets of
     * collisions in bins, we just XOR some shifted bits in the
     * cheapest possible way to reduce systematic lossage, as well as
     * to incorporate impact of the highest bits that would otherwise
     * never be used in index calculations because of table bounds.
     */
    static final int hash(Object key) {  //计算hash值
        int h;
        /**
         *  如果key为空, 则返回0;
         *  如果key不为空,则计算key的hash, 并且与该hash值的高16位进行异或运算减少hash碰撞 <=== hash值的扰动计算
         */
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }

    /**
     * Returns x's Class if it is of the form "class C implements
     * Comparable<C>", else null.
     * 如果目标对象x实现了Comparable接口, 则返回x的类对象
     */
    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c; Type[] ts, as; Type t; ParameterizedType p;
            if ((c = x.getClass()) == String.class) //如果是String类型, 不再检查, 直接返回
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {  //获取c实现的接口,包含接口中的泛型信息; ParameterizedType:参数化类型
                for (int i = 0; i < ts.length; ++i) { //循环遍历x的实现的所有接口(包括接口中的泛型), 判断是否存在Comparable,
                    if (((t = ts[i]) instanceof ParameterizedType) &&  //ParameterizedType: 参数化类型
                        ((p = (ParameterizedType)t).getRawType() ==
                         Comparable.class) &&
                        (as = p.getActualTypeArguments()) != null &&
                        as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        return null;
    }

    /**
     * Returns k.compareTo(x) if x matches kc (k's screened comparable
     * class), else 0.
     * 如果对象kc和k 实现了comparable接口, 则进行强转, 比较
     */
    @SuppressWarnings({"rawtypes","unchecked"}) // for cast to Comparable
    static int compareComparables(Class<?> kc, Object k, Object x) {
        /**
         * 先比较目标节点key与当前节点key的class对象是否一致
         * 如果一致, 再通过compareTo方法比较
         */
        return (x == null || x.getClass() != kc ? 0 : ((Comparable)k).compareTo(x));
    }

    /**
     * Returns a power of two size for the given target capacity.
     * 找到【大于等于】给定容量的最小2的次幂值
     * 例如: cap = 15, return 16;
     */
    static final int tableSizeFor(int cap) {
        int n = cap - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    /* ---------------- Fields -------------- */

    /**
     * The table, initialized on first use, and resized as
     * necessary. When allocated, length is always a power of two.
     * (We also tolerate length zero in some operations to allow
     * bootstrapping mechanics that are currently not needed.)
     */
    transient Node<K,V>[] table;  //桶; 存储链表的头节点的表, 或红黑树的根节点的表

    /**
     * Holds cached entrySet(). Note that AbstractMap fields are used
     * for keySet() and values().
     */
    transient Set<Map.Entry<K,V>> entrySet;  //??

    /**
     * The number of key-value mappings contained in this map.
     */
    transient int size;  //HashMap中实际存储数据的数量

    /**
     * The number of times this HashMap has been structurally modified
     * Structural modifications are those that change the number of mappings in
     * the HashMap or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the HashMap fail-fast.  (See ConcurrentModificationException).
     */
    transient int modCount;  //HashMap结构上被修改的次数

    /**
     * The next size value at which to resize (capacity * load factor).
     *
     * @serial
     */
    // (The javadoc description is true upon serialization.
    // Additionally, if the table array has not been allocated, this
    // field holds the initial array capacity, or zero signifying
    // DEFAULT_INITIAL_CAPACITY.)
    int threshold;  //阈值, 当size超过该阈值, 则进行扩容; ( 容量 * 负载系数 ) 16 * 0.75f = 12,

    /**
     * 负载因子 0.75
     * 负载因子为什么是0.75?
     *   https://segmentfault.com/a/1190000023308658
     *
     * 负载因子的用处, 最大可能的避免出现Hash冲突
     */
    final float loadFactor;

    /* ---------------- Public operations -------------- */

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and load factor.
     *
     * @param  initialCapacity the initial capacity
     * @param  loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *         or the load factor is nonpositive
     */
    public HashMap(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0)
            throw new IllegalArgumentException("Illegal initial capacity: " +
                                               initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)
            initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new IllegalArgumentException("Illegal load factor: " +
                                               loadFactor);
        this.loadFactor = loadFactor;
        this.threshold = tableSizeFor(initialCapacity);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and the default load factor (0.75).
     *
     * @param  initialCapacity the initial capacity.
     * @throws IllegalArgumentException if the initial capacity is negative.
     */
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the default initial capacity
     * (16) and the default load factor (0.75).
     */
    public HashMap() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }

    /**
     * Constructs a new <tt>HashMap</tt> with the same mappings as the
     * specified <tt>Map</tt>.  The <tt>HashMap</tt> is created with
     * default load factor (0.75) and an initial capacity sufficient to
     * hold the mappings in the specified <tt>Map</tt>.
     *
     * @param   m the map whose mappings are to be placed in this map
     * @throws  NullPointerException if the specified map is null
     */
    public HashMap(Map<? extends K, ? extends V> m) {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }

    /**
     * Implements Map.putAll and Map constructor
     *
     * @param m the map
     * @param evict false when initially constructing this map, else
     * true (relayed to method afterNodeInsertion).
     *   将给定map的所有元素放入当前的map中, 给定的map必须实现Map.putAll方法和Map的构造函数
     */
    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();  //给定map中的元素数量
        if (s > 0) {
            if (table == null) { // pre-size
                /**
                 * 此处根据给定map中实际元素的数量, 推算容纳下给定map中所有元素所需要的最小容量
                 * size <= threshold = capacity * 0.75
                 * 如果想要capacity取得最小值, 那么threshold等于size即可, 因此可以通过可以通过size直接推算最小容量
                 */
                float ft = ((float)s / loadFactor) + 1.0F;  //计算新的hash表能够容纳下给定map中所有元素所需要的最小capacity
                int t = ((ft < (float)MAXIMUM_CAPACITY) ? (int)ft : MAXIMUM_CAPACITY);

                if (t > threshold)  //如果最小容量大于当前hash的阈值, 则更新阈值为大于等于当前容量的最小2的等次幂 例:s = 3, t = 5, threshold = 8
                    /**
                     * 此处的threshold为新hash表的最小容量, 后面threshold将赋给newCap, 而threshold将根据newCap * 0.75重新计算
                     * 此处为什么要使用threshold来表示最小容量??
                     *
                     * Hash表的容量必须为2的等次幂, 所以此处需要计算大于等于期望容量的最小值
                     */
                    threshold = tableSizeFor(t);
            }
            else if (s > threshold)
                /**
                 * 如果当前hash表不为null,且单单给定map中的元素就超过了阈值, 则提前扩容, 在遍历插入, 在插入的过程中也有可能进行扩容
                 * 其他情况则在put的时候进行扩容
                 */
                resize();
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) { //遍历给定map,向当前map中put元素
                K key = e.getKey();
                V value = e.getValue();
                /**
                 * 向目标hash表中添加元素
                 */
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     *
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key==null ? k==null :
     * key.equals(k))}, then this method returns {@code v}; otherwise
     * it returns {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(Object, Object)
     */
    public V get(Object key) {
        Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? null : e.value;
    }

    /**
     *  根据key的hash值获取value
     */
    final Node<K,V> getNode(int hash, Object key) {
        Node<K,V>[] tab; Node<K,V> first, e; int n; K k;
        /**
         * hash表不为空且长度大于0
         * 获取到根据hash计算索引,获取到第一个节点(该节点可能为链表节点或者红黑树根节点)
         */
        if ((tab = table) != null && (n = tab.length) > 0 && (first = tab[(n - 1) & hash]) != null) {
            /**
             *  判断key是否相同的条件: 两个key的内存地址相同 或者 两个key通过equals方法判定为相同
             * 判断第一个节点是否是目标节点(注意:判断两个节点相同只能使用equals方法, 而compareTo()仅用于比较两个可比较节点的大小, 不能作为是否相同
             */
            if (first.hash == hash  &&  ((k = first.key) == key || (key != null && key.equals(k))) )
                return first;
            //如果头节点的下一个节点不为null才会去查找, 否则直接返回null
            if ((e = first.next) != null) {
                /**
                 * 1.如果头节点为红黑树节点, 需要到红黑树找
                 *   调用红黑树的方法获取并返回指定key的节点
                 */
                if (first instanceof TreeNode)
                    return ((TreeNode<K,V>)first).getTreeNode(hash, key);
                /**
                 * 2. 如果头节点为链表, 循环遍历链表寻找目标节点
                 */
                do {
                    if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
                        return e;
                } while ((e = e.next) != null);
            }
        }
        return null;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the
     * specified key.
     *
     * @param   key   The key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified
     * key.
     */
    public boolean containsKey(Object key) {
        return getNode(hash(key), key) != null;
    }

    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old
     * value is replaced.
     *
     * @param key key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    /**
     * Implements Map.put and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @param value the value to put
     * @param onlyIfAbsent if true, don't change existing value
     * @param evict if false, the table is in creation mode.
     * @return previous value, or null if none
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent, boolean evict) {
        Node<K,V>[] tab;
        Node<K,V> p;
        int n, i;  //n: hash表的长度; i: 目标key在hash表中的索引
        if ((tab = table) == null || (n = tab.length) == 0)
           /**
            * 如果当前hash表为空, 或者长度为0 则初始化 【懒加载】
            */
            n = (tab = resize()).length;
        if ((p = tab[i = (n - 1) & hash]) == null)
            /**
             * 如果对应hash桶的位置没有节点, 那么直接将当前节点放到此位置中
             * p为当前节点key的hash的索引值所对应的桶节点, 在判断语句中已经进行赋值操作
             */
            tab[i] = newNode(hash, key, value, null);
        else {
            Node<K,V> e; K k;
            /**
             * 如果当前桶节点的hash值与新增节点的hash值相同, 并且key也相同, 即覆盖当前节点的value即可
             */
            if (p.hash == hash && ((k = p.key) == key || (key != null && key.equals(k))))
                e = p;
            /**
             * 【程序执行到这里】: 当前桶节点的key与新增节点的key不相同
             * 红黑树节点处理
             */
            else if (p instanceof TreeNode)
                e = ((TreeNode<K,V>)p).putTreeVal(this, tab, hash, key, value); //如果在红黑树中存在相同key的节点, 那么这里会返回该节点, 便于后面统一进行覆盖操作
            /**
             * 链表节点处理
             */
            else {
                for (int binCount = 0; ; ++binCount) {  //计算当前链表的长度, 后面判断如果大于8, 需要转为红黑树
                    /**
                     * 如果查找至链表尾部, 还未找到相同key, 那么直接添加至尾部即可;
                     * 这个也就是为什么新增的节点需要插入到链表尾部, 反正都要到达链表尾部的
                     */
                    if ((e = p.next) == null) {
                        p.next = newNode(hash, key, value, null);
                        /**
                         * 这里为什么要对TREEIFY_THRESHOLD-1?
                         * 因为在本次插入节点后, 链表的长度已经增长了1
                         */
                        if (binCount >= TREEIFY_THRESHOLD - 1)
                            /**
                             * 符合调条件, 当前链表可能需要转为红黑树
                             */
                            treeifyBin(tab, hash);
                        break;
                    }
                    if (e.hash == hash && ((k = e.key) == key || (key != null && key.equals(k))))
                        /**
                         * 【当程序执行到这里】: 待插入节点与链表中的某个节点的key一致! 因为在并发场景中, 可能在插入新节点之前其他线程已经插入了一个与当前节点相同key的节点,
                         * 为了保证hashmap中key的唯一性, 所以需要做最后的校验
                         */
                        break;
                    p = e;
                } //for
            }
            /**
             * 【当程序执行到这里】: 如果e不为null, 那么说明在hashmap中存在于待插入的节点相同的key, 那么只需要覆盖该节点的value值即可
             */
            if (e != null) { // existing mapping for key
                V oldValue = e.value;
                if (!onlyIfAbsent || oldValue == null)
                    /**
                     * 如果允许覆盖旧的value 或者 旧的value为bull 才会进行覆盖
                     */
                    e.value = value;
                afterNodeAccess(e);  //linkedHashMap实现
                return oldValue; //返回覆盖的旧value值
            }
        }
        ++modCount;
        /**
         * 在添加新的元素后, 判断是否超过阈值, 如果超过, 则进行扩容
         */
        if (++size > threshold)
            resize();
        afterNodeInsertion(evict);//linkedHashMap实现
        return null;
    }

    /**
     * Initializes or doubles table size.  If null, allocates in
     * accord with initial capacity target held in field threshold.
     * Otherwise, because we are using power-of-two expansion, the
     * elements from each bin must either stay at same index, or move
     * with a power of two offset in the new table.
     *
     * @return the table
     */
    final Node<K,V>[] resize() {
        Node<K,V>[] oldTab = table;
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        int oldThr = threshold;
        int newCap, newThr = 0;
        if (oldCap > 0) {
            /**
             *  旧hash表进行扩容
             */
            if (oldCap >= MAXIMUM_CAPACITY) {
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY && oldCap >= DEFAULT_INITIAL_CAPACITY)
                /**
                 * 新容量与新阈值均扩展为原数值的两倍
                 */
                newThr = oldThr << 1; // double threshold
        }
        else if (oldThr > 0) // initial capacity was placed in threshold
            /**
             * 【程序执行到这里】: 目标hash表的旧容量为空, 但是旧阈值不为空, 也就说明此时是需要进行初始化的
             *  而旧的阈值oldThr 就是 提前计算好需要的hash表的初始化容量
             */
            newCap = oldThr;
        else {
            /**
             * 【程序执行到这里】: 目标hash表的旧容量和旧阈值均为空, 需要将容量和阈值设置为默认值
             */
            newCap = DEFAULT_INITIAL_CAPACITY;  //默认容量:16
            newThr = (int)(DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);  //默认阈值:12
        }

        if (newThr == 0) {
            /**
             * 【程序执行到这里】: 新的容量已经计算出来, 但是新的阈值还未进行计算
             */
            float ft = (float)newCap * loadFactor;  //新的容量 * 负载因子 = 新的阈值
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float)MAXIMUM_CAPACITY ?
                      (int)ft : Integer.MAX_VALUE);
        }
        threshold = newThr; //更新阈值
        /**
         * 根据新的容量创建hash表
         */
        @SuppressWarnings({"rawtypes","unchecked"})
            Node<K,V>[] newTab = (Node<K,V>[])new Node[newCap];
        table = newTab;
        /**
         * 如果就得hash表不为空, 那么需要进行元素挪动, 即需要把旧的hash表上的元素挪到新的hash表上
         */
        if (oldTab != null) {
            /**
             * 遍历旧的hash表的所有桶节点, 开始挪动元素
             */
            for (int j = 0; j < oldCap; ++j) {
                Node<K,V> e;  // e: 准备挪动的节点
                //如果该桶节点不为空,则开始挪动
                if ((e = oldTab[j]) != null) {
                    oldTab[j] = null;  //清除原桶节点的引用
                    if (e.next == null)
                        /**
                         * 如果桶节点的下一个节点为空, 那么说明该hash桶中只有一个节点, 直接计算新的索引, 然后挪动就可以了
                         *  注意:如果在旧的hash表中某个桶的位置只有一个元素, 那么在新的hash表中, 该元素所对应的新的hash桶位置也将只有一个元素
                         */
                        newTab[e.hash & (newCap - 1)] = e;
                    else if (e instanceof TreeNode)
                        /**
                         * 如果当前节点是红黑树节点, 则强转为TreeNode节点, 利用红黑树性质挪动节点
                         */
                        ((TreeNode<K,V>)e).split(this, newTab, j, oldCap);
                    else { // 保持顺序
                        /**
                         * 如果当前节点是链表节点
                         */
                        Node<K,V> loHead = null, loTail = null;  //lohead: 链表头节点, loTail链表尾节点
                        Node<K,V> hiHead = null, hiTail = null;
                        Node<K,V> next;
                        do {
                            next = e.next;  //获取当前节点的下一个节点
                            if ((e.hash & oldCap) == 0) {
                                if (loTail == null)
                                    loHead = e;
                                else
                                    loTail.next = e;
                                loTail = e;
                            }
                            else {
                                if (hiTail == null)
                                    hiHead = e;
                                else
                                    hiTail.next = e;
                                hiTail = e;
                            }
                        } while ((e = next) != null);
                        if (loTail != null) {
                            loTail.next = null;
                            newTab[j] = loHead;
                        }
                        if (hiTail != null) {
                            hiTail.next = null;
                            newTab[j + oldCap] = hiHead;
                        }
                    }
                }
            }
        }
        return newTab;
    }

    /**
     * Replaces all linked nodes in bin at index for given hash unless
     * table is too small, in which case resizes instead.
     */
    final void treeifyBin(Node<K,V>[] tab, int hash) {
        int n, index; Node<K,V> e;  //n:hash表的长度, index:新增节点在hash表中索引位置, e:桶节点
        /**
         * 如果hash表为null 或者 hash表的长度大于等于最小红黑树容量 (也就是hash表中出现红黑树需要达到的最小容量)才会将链表转换为红黑树
         */
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            //如果小于, 则进行的是【扩容操作】, 而不是转换红黑树
            resize();
        /**
         * 符合转红黑树条件
         *    【1】:链表长度超过8
         *    【2】:hash表的长度大于最小红黑树容量64
         *
         *    (n - 1) & hash  ==> 取模,获取索引
         */
        else if ((e = tab[index = (n - 1) & hash]) != null) {
            /**
             * 如果当前桶节点不为空
             * 前面已经判断过该桶节点不为空了, 此处为什么还要再次判断 ?
             * 因为, hashmap中有可能是存在并发操作....
             */
            TreeNode<K,V> hd = null, tl = null;  //td: 链表的第一个节点
            do {
                /**
                 * 将链表中Node节点转为TreeNode节点
                 * 由于之前是链表, 所以该链表的所有节点均为Node, 但是, 接下来需要转为红黑树了, 就不能再使用Node节点, 而是TreeNode节点
                 */
                TreeNode<K,V> p = replacementTreeNode(e, null);
                if (tl == null)
                    hd = p;  //获取到链表节点转红黑树节点后的第一个节点, 后面需要根据这个节点将链表转为红黑树
                else {
                    p.prev = tl;  //维护红黑树节点中的prev属性
                    tl.next = p;  //维护链表中的next属性
                }
                tl = p;
            } while ((e = e.next) != null);

            /**
             * 链表转红黑树
             */
            if ((tab[index] = hd) != null)
                hd.treeify(tab);  //this为链表的第一个节点
        }
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }

    /**
     * Removes the mapping for the specified key from this map if present.
     *
     * @param  key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V remove(Object key) {
        Node<K,V> e;
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
            null : e.value;
    }

    /**
     * Implements Map.remove and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @param value the value to match if matchValue, else ignored
     * @param matchValue if true only remove if value is equal
     * @param movable if false do not move other nodes while removing
     * @return the node, or null if none
     */
    final Node<K,V> removeNode(int hash, Object key, Object value,
                               boolean matchValue, boolean movable) {
        Node<K,V>[] tab; Node<K,V> p; int n, index;
        if ((tab = table) != null && (n = tab.length) > 0 &&
            (p = tab[index = (n - 1) & hash]) != null) {
            Node<K,V> node = null, e; K k; V v;
            if (p.hash == hash &&
                ((k = p.key) == key || (key != null && key.equals(k))))
                node = p;
            else if ((e = p.next) != null) {
                if (p instanceof TreeNode)
                    node = ((TreeNode<K,V>)p).getTreeNode(hash, key);
                else {
                    do {
                        if (e.hash == hash &&
                            ((k = e.key) == key ||
                             (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }
            if (node != null && (!matchValue || (v = node.value) == value ||
                                 (value != null && value.equals(v)))) {
                if (node instanceof TreeNode)
                    ((TreeNode<K,V>)node).removeTreeNode(this, tab, movable);
                else if (node == p)
                    tab[index] = node.next;
                else
                    p.next = node.next;
                ++modCount;
                --size;
                afterNodeRemoval(node);
                return node;
            }
        }
        return null;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear() {
        Node<K,V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0) {
            size = 0;
            for (int i = 0; i < tab.length; ++i)
                tab[i] = null;
        }
    }

    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     *         specified value
     */
    public boolean containsValue(Object value) {
        Node<K,V>[] tab; V v;
        if ((tab = table) != null && size > 0) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    if ((v = e.value) == value ||
                        (value != null && value.equals(v)))
                        return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation), the results of
     * the iteration are undefined.  The set supports element removal,
     * which removes the corresponding mapping from the map, via the
     * <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt>, and <tt>clear</tt>
     * operations.  It does not support the <tt>add</tt> or <tt>addAll</tt>
     * operations.
     *
     * @return a set view of the keys contained in this map
     */
    public Set<K> keySet() {
        Set<K> ks;
        return (ks = keySet) == null ? (keySet = new KeySet()) : ks;
    }

    final class KeySet extends AbstractSet<K> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<K> iterator()     { return new KeyIterator(); }
        public final boolean contains(Object o) { return containsKey(o); }
        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }
        public final Spliterator<K> spliterator() {
            return new KeySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super K> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.key);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own <tt>remove</tt> operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a view of the values contained in this map
     */
    public Collection<V> values() {
        Collection<V> vs;
        return (vs = values) == null ? (values = new Values()) : vs;
    }

    final class Values extends AbstractCollection<V> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<V> iterator()     { return new ValueIterator(); }
        public final boolean contains(Object o) { return containsValue(o); }
        public final Spliterator<V> spliterator() {
            return new ValueSpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super V> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.value);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation, or through the
     * <tt>setValue</tt> operation on a map entry returned by the
     * iterator) the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and
     * <tt>clear</tt> operations.  It does not support the
     * <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a set view of the mappings contained in this map
     */
    public Set<Map.Entry<K,V>> entrySet() {
        Set<Map.Entry<K,V>> es;
        return (es = entrySet) == null ? (entrySet = new EntrySet()) : es;
    }

    final class EntrySet extends AbstractSet<Map.Entry<K,V>> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<Map.Entry<K,V>> iterator() {
            return new EntryIterator();
        }
        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?,?> e = (Map.Entry<?,?>) o;
            Object key = e.getKey();
            Node<K,V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }
        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }
        public final Spliterator<Map.Entry<K,V>> spliterator() {
            return new EntrySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super Map.Entry<K,V>> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    // Overrides of JDK8 Map extension methods

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }

    @Override
    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }

    @Override
    public boolean remove(Object key, Object value) {
        return removeNode(hash(key), key, value, true, true) != null;
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        Node<K,V> e; V v;
        if ((e = getNode(hash(key), key)) != null &&
            ((v = e.value) == oldValue || (v != null && v.equals(oldValue)))) {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }

    @Override
    public V replace(K key, V value) {
        Node<K,V> e;
        if ((e = getNode(hash(key), key)) != null) {
            V oldValue = e.value;
            e.value = value;
            afterNodeAccess(e);
            return oldValue;
        }
        return null;
    }

    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null) {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null) {
            return null;
        } else if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        else if (t != null)
            t.putTreeVal(this, tab, hash, key, v);
        else {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1)
                treeifyBin(tab, hash);
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        Node<K,V> e; V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
            (oldValue = e.value) != null) {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null) {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
            else
                removeNode(hash, key, null, false, true);
        }
        return null;
    }

    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
        }
        else if (v != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, v);
            else {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }

    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null)
            throw new NullPointerException();
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null) {
            V v;
            if (old.value != null)
                v = remappingFunction.apply(old.value, value);
            else
                v = value;
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
            return v;
        }
        if (value != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, value);
            else {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        Node<K,V>[] tab;
        if (action == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next)
                    action.accept(e.key, e.value);
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        Node<K,V>[] tab;
        if (function == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    /* ------------------------------------------------------------ */
    // Cloning and serialization

    /**
     * Returns a shallow copy of this <tt>HashMap</tt> instance: the keys and
     * values themselves are not cloned.
     *
     * @return a shallow copy of this map
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object clone() {
        HashMap<K,V> result;
        try {
            result = (HashMap<K,V>)super.clone();
        } catch (CloneNotSupportedException e) {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();
        result.putMapEntries(this, false);
        return result;
    }

    // These methods are also used when serializing HashSets
    final float loadFactor() { return loadFactor; }
    final int capacity() {
        return (table != null) ? table.length :
            (threshold > 0) ? threshold :
            DEFAULT_INITIAL_CAPACITY;
    }

    /**
     * Save the state of the <tt>HashMap</tt> instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData The <i>capacity</i> of the HashMap (the length of the
     *             bucket array) is emitted (int), followed by the
     *             <i>size</i> (an int, the number of key-value
     *             mappings), followed by the key (Object) and value (Object)
     *             for each key-value mapping.  The key-value mappings are
     *             emitted in no particular order.
     */
    private void writeObject(java.io.ObjectOutputStream s)
        throws IOException {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }

    /**
     * Reconstitute the {@code HashMap} instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(java.io.ObjectInputStream s)
        throws IOException, ClassNotFoundException {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new InvalidObjectException("Illegal load factor: " +
                                             loadFactor);
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                                             mappings);
        else if (mappings > 0) { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float)mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                       DEFAULT_INITIAL_CAPACITY :
                       (fc >= MAXIMUM_CAPACITY) ?
                       MAXIMUM_CAPACITY :
                       tableSizeFor((int)fc));
            float ft = (float)cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                         (int)ft : Integer.MAX_VALUE);
            @SuppressWarnings({"rawtypes","unchecked"})
                Node<K,V>[] tab = (Node<K,V>[])new Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++) {
                @SuppressWarnings("unchecked")
                    K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                    V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }

    /* ------------------------------------------------------------ */
    // iterators

    abstract class HashIterator {
        Node<K,V> next;        // next entry to return
        Node<K,V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            Node<K,V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {} while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K,V> nextNode() {
            Node<K,V>[] t;
            Node<K,V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {} while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            Node<K,V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class KeyIterator extends HashIterator
        implements Iterator<K> {
        public final K next() { return nextNode().key; }
    }

    final class ValueIterator extends HashIterator
        implements Iterator<V> {
        public final V next() { return nextNode().value; }
    }

    final class EntryIterator extends HashIterator
        implements Iterator<Map.Entry<K,V>> {
        public final Map.Entry<K,V> next() { return nextNode(); }
    }

    /* ------------------------------------------------------------ */
    // spliterators

    static class HashMapSpliterator<K,V> {
        final HashMap<K,V> map;
        Node<K,V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMap<K,V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                HashMap<K,V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                Node<K,V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }

    static final class KeySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<K> {
        KeySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                       int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public KeySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                                        expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super K> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    static final class ValueSpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<V> {
        ValueSpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public ValueSpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super V> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }

    static final class EntrySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<Map.Entry<K,V>> {
        EntrySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public EntrySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K,V>> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        Node<K,V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    /* ------------------------------------------------------------ */
    // LinkedHashMap support


    /*
     * The following package-protected methods are designed to be
     * overridden by LinkedHashMap, but not by any other subclass.
     * Nearly all other internal methods are also package-protected
     * but are declared final, so can be used by LinkedHashMap, view
     * classes, and HashSet.
     */

    // Create a regular (non-tree) node
    Node<K,V> newNode(int hash, K key, V value, Node<K,V> next) {
        return new Node<>(hash, key, value, next);
    }

    // For conversion from TreeNodes to plain nodes
    Node<K,V> replacementNode(Node<K,V> p, Node<K,V> next) {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    // Create a tree bin node
    TreeNode<K,V> newTreeNode(int hash, K key, V value, Node<K,V> next) {
        return new TreeNode<>(hash, key, value, next);
    }

    // 根据普通Node节点生成一个红黑树节点
    TreeNode<K,V> replacementTreeNode(Node<K,V> p, Node<K,V> next) {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    /**
     * Reset to initial default state.  Called by clone and readObject.
     */
    void reinitialize() {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }

    // Callbacks to allow LinkedHashMap post-actions
    void afterNodeAccess(Node<K,V> p) { }
    void afterNodeInsertion(boolean evict) { }
    void afterNodeRemoval(Node<K,V> p) { }

    // Called only from writeObject, to ensure compatible ordering.
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        Node<K,V>[] tab;
        if (size > 0 && (tab = table) != null) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }

    /* ------------------------------------------------------------ */
    // Tree bins

    /**
     * Entry for Tree bins. Extends LinkedHashMap.Entry (which in turn
     * extends Node) so can be used as extension of either regular or
     * linked node.
     *
     * 红黑树节点
     */
    static final class TreeNode<K,V> extends LinkedHashMap.Entry<K,V> {
        TreeNode<K,V> parent;  // 父节点
        TreeNode<K,V> left;    //左子节点
        TreeNode<K,V> right;   //右子节点
        TreeNode<K,V> prev;    // 维持红黑树中节点的添加顺序 (注意: 在删除节点后, 需要取消连接)
        boolean red;           // 红黑树节点颜色, 默认为红色
        TreeNode(int hash, K key, V val, Node<K,V> next) {
            super(hash, key, val, next);
        }

        /**
         * 返回节点的根节点
         */
        final TreeNode<K,V> root() {
            for (TreeNode<K,V> r = this, p;;) {
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }

        /**
         * Ensures that the given root is the first node of its bin.
         * 【1】 将红黑树的root节点移动到hash表相对应的索引位置
         * 【2】 将红黑树的root节点维护到链表的第一个节点
         * 通过moveRootToFront方法, root节点即使红黑树的根节点, 也是原链表的第一个节点
         */
        static <K,V> void moveRootToFront(Node<K,V>[] tab, TreeNode<K,V> root) {
            int n;
            if (root != null && tab != null && (n = tab.length) > 0) {
                // 计算索引
                int index = (n - 1) & root.hash;
                // 原链表的头节点
                TreeNode<K,V> first = (TreeNode<K,V>)tab[index];
                /**
                 * 如果该索引位置的头节点不是root节点，则该索引位置的头节点替换为root节点
                 */
                if (root != first) {
                    Node<K,V> rn;  //rn:后一个节点
                    //将该索引位置的头节点赋值为root节点
                    tab[index] = root;
                    TreeNode<K,V> rp = root.prev; //root节点前一个节点
                    /**
                     * 删除root节点在原有链表中前后引用关系, 将root节点从链表中"删除", 因为后面要将root节点添加到链表的头部
                     */
                    // 如果root节点的next节点不为空，则将root节点的next节点的prev属性设置为root节点的prev节点
                    if ((rn = root.next) != null)
                        ((TreeNode<K,V>)rn).prev = rp;
                    // 如果root节点的prev节点不为空，则将root节点的prev节点的next属性设置为root节点的next节点
                    if (rp != null)
                        rp.next = rn;
                    /**
                     * 将原有链表的第一个节点设为root节点的下一个节点
                     */
                    if (first != null)
                        // 如果原头节点不为空, 则将原头节点的prev属性设置为root节点
                        first.prev = root;
                    // root的next指向头节点
                    root.next = first;
                    // root的prev指向null
                    root.prev = null;
                }
                /**
                 * 这一步是防御性的编程
                 * 校验TreeNode对象是否满足红黑树和双链表的特性
                 * 如果这个方法校验不通过：可能是因为用户编程失误，破坏了结构（例如：并发场景下）；也可能是TreeNode的实现有问题（这个是理论上的以防万一）；
                 **/
                assert checkInvariants(root);
            }
        }

        /**
         * Finds the node starting at root p with the given hash and key.
         * The kc argument caches comparableClassFor(key) upon first use
         * comparing keys.
         *
         * 在红黑树中查找指定节点
         *
         *  注意: 在find方法中比较的是hash值大小, 在某棵红黑树中, 所有的节点在hash表中的索引是一样的, 但是hash值不一定相同
         */
        final TreeNode<K,V> find(int h, Object k, Class<?> kc) {
            TreeNode<K,V> p = this;   //this: 当前节点, h:目标key的hash值, k:目标节点的key, kc:
            do {
                int ph, dir;  //ph: 当前节点的hash值; dir:
                K pk;  //当前节点的key
                TreeNode<K,V> pl = p.left, pr = p.right, q;  //pl当前节点的左子节点, pr当前节点的右子节点
                /**
                 * 获取当前节点的hash值, 比较hash值
                 * 如果目标key的hash小于当前节点key的hash值, 则向该红黑树的左子树查找
                 */
                if ((ph = p.hash) > h)
                    p = pl;
                /**
                 * 如果目标key的hash大于当前节点key的hash值, 则向该红黑树的右子树查找
                 */
                else if (ph < h)
                    p = pr;
                /**
                 *  【程序到达这里】: 当前节点与目标节点hash值相同, 开始判定key是否相同:
                 *  key相同需要满足的条件:
                 *     1.目标key的hash等于当前节点key的hash值
                 *     2.当前节点的key与目标节点的key内存地址相同 或者 当前节点的key与目标节点的key通过equals判定为相同
                 */
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                /**
                 * 【程序到达这里】: 当前节点与目标节点hash值相同, 但是key不相同, 也就是目标节点可能在当前的节点子树中;
                 *   思考: 此时当前节点的hash值与目标节点的hash值相同, 但是又不是同一个节点, 那么
                 *       接下来需要接着向下查找, 但是由于hash值相同, 将无法判断目标节点在当前的节点的
                 *       左子树还是右子树中, 所以如果节点存在可比较性, 将根据compareTo方法进行比较;如
                 *       若节点不存在可比较性, 那么将采用层序遍历, 向下逐个查找;
                 *
                 *  当前节点的左子节点为null,即不存在左子树, 那么将准备在当前节点的右子树中查找目标key
                 */
                else if (pl == null)
                    p = pr;
                /**
                 *  当前节点的右子节点为null,即不存在右子树, 那么将准备在当前节点的左子树中查找目标key
                 */
                else if (pr == null)
                    p = pl;
                /**
                 * 【程序到达这里】: 当前节点的左右子树都不为空, 那么需要判断节点是否具有可比较性
                 */
                else if ( (kc != null || (kc = comparableClassFor(k)) != null) //判断key是否具有可比较性(是否实现Comparable接口)
                          &&
                         (dir = compareComparables(kc, k, pk)) != 0 )  //dir: 目标节点key与当前节点key比较的差值
                    /**
                     * 如果dir小于0, 说明目标节点key小于当前节点key,那么将开始向当前节点的左子树中查找
                     * 如果dir大于0, 说明目标节点key大于当前节点key,那么将开始向当前节点的右子树中查找
                     */
                    p = (dir < 0) ? pl : pr;
                /**
                 * 如果dir等于0, 说明目标节点key的大小等于当前节点key的大小, 但是不能判定为两个key相同,
                 * 两个key相同只能通过内存地址,或者equals方法判断; 如果dir==0, 那么将开始分别向左右子树中查找;
                 *
                 * 默认向开始递归向当前节点的右子树中查找, 如果找到则直接返回, 如果没有找到,则开始向左子树中查找
                 */
                else if ((q = pr.find(h, k, kc)) != null)
                    return q;
                else
                    p = pl;
            } while (p != null);
            return null;
        }

        /**
         * Calls find for root node.
         */
        final TreeNode<K,V> getTreeNode(int h, Object k) {
            /**
             * 找到当前节点的根节点, 然后开始查找指定节点
             */
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /**
         * Tie-breaking utility for ordering insertions when equal
         * hashCodes and non-comparable. We don't require a total
         * order, just a consistent insertion rule to maintain
         * equivalence across rebalancings. Tie-breaking further than
         * necessary simplifies testing a bit.
         */
        static int tieBreakOrder(Object a, Object b) {
            int d;
            /**
             * a,b:待比较对象
             * 如果a,b为null, 或者a,b通过compareTo()方法比较认定为大小相同, 那么将比较两个对象内存地址hash值的大小
             */
            if (a == null || b == null || (d = a.getClass().getName().compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ? -1 : 1);
            return d;
        }

        /**
         * Forms tree of the nodes linked from this node.
         * @return root of tree
         */
        final void treeify(Node<K,V>[] tab) {
            TreeNode<K,V> root = null; //初始化红黑树的根节点为null
            /**
             * 从链表的第一个节点开始遍历, 转换
             */
            for (TreeNode<K,V> x = this, next; x != null; x = next) {
                next = (TreeNode<K,V>)x.next; //next: 当前节点的下一个节点
                x.left = x.right = null;  //初始化当前节点左右子节点都为null
                /**
                 * 如果root节点未确认, 那么将当前节点作为根节点, 并置为黑色(红黑树性质:根节点为黑色)
                 */
                if (root == null) {
                    x.parent = null;
                    x.red = false;
                    root = x;
                }
                /**
                 * 【当程序执行到这里】: root节点已经确认, 第一次执行到else中时, x节点为此时root节点在链表中的下一个节点
                 * 生成红黑树
                 */
                else {
                    K k = x.key;     //当前节点的key
                    int h = x.hash;  //当前节点key的hash值
                    Class<?> kc = null;  //可比较节点的类对象
                    /**
                     * 每次都需要从根节点开始找到合适的位置插入当前节点
                     * 在查找过程中不需要判断当前节点是否与红黑树中的节点通过equals判定为相同
                     */
                    for (TreeNode<K,V> p = root;;) {
                        int dir, ph;   //dir: 当前节点与根节点大小差值, ph: 根节点节点的hash值
                        K pk = p.key;  //根节点节点的key
                        /**
                         * 判断当前节点需要插入到根节点的左子树还是右子树中
                         */
                        if ((ph = p.hash) > h)
                            dir = -1;
                        else if (ph < h)
                            dir = 1;
                        /**
                         * 如果当前节点与根节点key的hash值相同, 则判断是否具有可比较性, 根据compareTo方法判断大小
                         */
                        else if ( (kc == null && (kc = comparableClassFor(k)) == null) ||
                                 (dir = compareComparables(kc, k, pk)) == 0 )
                            /**
                             * 如果当前节点与根节点不具备可比较性, 或者具备可比较性,但是被compareTo方法判定为大小相同
                             * 则比较两个节点key内存地址的hash值大小
                             */
                            dir = tieBreakOrder(k, pk);

                        /**
                         * 【当程序执行到这里】: 已经判断了根节点与当前节点的大小, 接下来根据差值, 判断是向根节点的左子树中插入还是右子树中插入
                         */
                        TreeNode<K,V> xp = p;
                        /**
                         * 根据差值判断是向根节点的左子树是右子树中查找, 并且是否到达最底层, 无法再向下查找; 如果没有到达最底层, 那么需要在该树中继续向下查找
                         */
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            /**
                             * 找到合适的节点位置, 开始插入
                             * 注意在转为红黑树后, 节点中仍然维护着链表中原有的prev属性
                             */
                            x.parent = xp;
                            if (dir <= 0)
                                xp.left = x;
                            else
                                xp.right = x;
                            /**
                             * 在插入后,修复红黑树性质
                             */
                            root = balanceInsertion(root, x);
                            break;
                        }
                    }
                } //else

            } //for

            /**
             * 将红黑树的root节点移动到hash表相对应的索引位置
             */
            moveRootToFront(tab, root);
        }

        /**
         * Returns a list of non-TreeNodes replacing those linked from
         * this node.
         */
        final Node<K,V> untreeify(HashMap<K,V> map) {
            Node<K,V> hd = null, tl = null;
            for (Node<K,V> q = this; q != null; q = q.next) {
                Node<K,V> p = map.replacementNode(q, null);
                if (tl == null)
                    hd = p;
                else
                    tl.next = p;
                tl = p;
            }
            return hd;
        }

        /**
         *  向红黑树中添加元素
         */
        final TreeNode<K,V> putTreeVal(HashMap<K,V> map, Node<K,V>[] tab, int h, K k, V v) {
            //map: 当前hashmap实例, tab: hash表, h: key的hash值, k: key值, v:value值
            Class<?> kc = null;
            boolean searched = false;  //是否进行了全局扫描搜索 (全局扫描的目的:是否已经存在即将插入的节点key)
            TreeNode<K,V> root = (parent != null) ? root() : this;  //确保传入当前节点为根节点
            /**
             * 从根节点开始遍历, 找到正确的插入位置
             */
            for (TreeNode<K,V> p = root;;) {
                int dir, ph; K pk; //dir: 新增节点与当前节点大小比较的差值, ph: 当前节点的hash值, pk: 当前节点的key, p:当前节点(待比较节点)
                /**
                 * 新增节点key的hash值 小于 当前节点key的hash值, 说明新增节点需要在当前的左树中插入
                 */
                if ((ph = p.hash) > h)
                    dir = -1;
                /**
                 * 新增节点key的hash值 大于 当前节点key的hash值, 说明新增节点需要在当前的右树中插入
                 */
                else if (ph < h)
                    dir = 1;
                /**
                 *  如果新增节点key的hash值与当前节点的hash值相等, 那么需要比较key是否相同(比较两个key的地址以及 使用equals方法判定); 如果相同, 则返回该节点
                 *  【注意】:此处没有覆盖操作, 这里仅仅返回重复节点, 在putVal方法中后面会统一进行覆盖value操作
                 */
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                /**
                 * 【程序执行到这里】: 新增节点key的hash值与当前节点的hash值相等, 但是key并不相等
                 *
                 *  需要判断两个节点是否具有可比较性
                 * 如果具有可比较性, 那么进行比较, 判断大小, 来决定接下来新增节点是在当前节点的左子树还是右子树中插入;
                 */
                else if (
                        (kc == null && (kc = comparableClassFor(k)) == null)  //两个节点不具备可比较性
                           ||
                        (dir = compareComparables(kc, k, pk)) == 0) {         //两个节点具备可比较性, 但是通过比较方法判定两个节点的key大小相等
                    /**
                     * 对当前节点的左子树和右子树进行全局扫描, 判断新增节点key是否已经存在
                     *   1.两个节点不具备可比较性
                     *   2.两个节点具备可比较性, 但是通过比较方法判定两个节点的key大小相等
                     *
                     * 【注意】:此处比较大小, 只能比较两个key的大小, 不能判定两个key相同, 两个key相同只能使用equals()方法判定 或者 内存地址一致
                     */
                    if (!searched) {
                        TreeNode<K,V> q, ch;
                        searched = true;  // 全局扫描比较消耗性能, 所以只进行一次即可
                        if (  ( (ch = p.left) != null && (q = ch.find(h, k, kc)) != null )  //在当前节点的左子树中查找是否存在新增节点的key
                                ||
                              ( (ch = p.right) != null && (q = ch.find(h, k, kc)) != null )   ) //在当前节点的右子树中查找是否存在新增节点的key
                            return q;
                    }
                    /**
                     * 【程序执行到这里】: 此时新增节点已经明确不存在于当前红黑树中, 所以需要判断接下来需要插入到当前节点的左子树还是右子树中
                     * 由于新增节点和当前节点不具有可比较性, 那么只能通过两个key的内存地址的hash值大小来比较
                     */
                    dir = tieBreakOrder(k, pk);
                }

                /**
                 * 【程序执行到这里】:  已经确认新增节点需要向当前节点左子树中插入还是右子树中插入, 那么接下来开始准备下一轮的判断
                 */
                TreeNode<K,V> xp = p;  //xp: 当前节点
                /**
                 * 如果已定位至当前节点 ,那么需要根据新增节点与当前节点大小的差值, 判断新增节点为该叶子节点的左子节点还是右子节点
                 */
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    Node<K,V> xpn = xp.next;  //xpn: 当前节点的下一个节点
                    TreeNode<K,V> x = map.newTreeNode(h, k, v, xpn);  //根据key,value创建新节点, 准备插入, x: 新增节点
                    if (dir <= 0)
                        xp.left = x; //新增节点为当前节点的左子节点
                    else
                        xp.right = x;  //新增节点为当前节点的右子节点
                    xp.next = x;  //新增节点为当前节点的下一个节点
                    x.parent = x.prev = xp;  //新增节点的前一个节点和父节点都为当前节点
                    if (xpn != null)  //维护原来当前节点的下一个节点的前一个节点为新增节点
                        ((TreeNode<K,V>)xpn).prev = x;
                    /**
                     * 在插入节点后, 修复红黑树
                     */
                    moveRootToFront(tab, balanceInsertion(root, x));
                    return null;
                }

            } //for循环结束
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         */
        final void removeTreeNode(HashMap<K,V> map, Node<K,V>[] tab,
                                  boolean movable) {
            int n;
            if (tab == null || (n = tab.length) == 0)
                return;
            int index = (n - 1) & hash;
            TreeNode<K,V> first = (TreeNode<K,V>)tab[index], root = first, rl;
            TreeNode<K,V> succ = (TreeNode<K,V>)next, pred = prev;
            if (pred == null)
                tab[index] = first = succ;
            else
                pred.next = succ;
            if (succ != null)
                succ.prev = pred;
            if (first == null)
                return;
            if (root.parent != null)
                root = root.root();
            if (root == null || root.right == null ||
                (rl = root.left) == null || rl.left == null) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            TreeNode<K,V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null) {
                TreeNode<K,V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red; s.red = p.red; p.red = c; // swap colors
                TreeNode<K,V> sr = s.right;
                TreeNode<K,V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else {
                    TreeNode<K,V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p) {
                TreeNode<K,V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            TreeNode<K,V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p) {  // detach
                TreeNode<K,V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        /**
         * Splits nodes in a tree bin into lower and upper tree bins,
         * or untreeifies if now too small. Called only from resize;
         * see above discussion about split bits and indices.
         *
         * @param map the map
         * @param tab the table for recording bin heads
         * @param index the index of the table being split
         * @param bit the bit of hash to split on
         */
        final void split(HashMap<K,V> map, Node<K,V>[] tab, int index, int bit) {
            //map: 当前hashmap对象, tab: 新的hash表, index:当前节点所在hash表中位置, bit:旧容量
            TreeNode<K,V> b = this;
            // Relink into lo and hi lists, 保持节点顺序
            TreeNode<K,V> loHead = null, loTail = null;
            TreeNode<K,V> hiHead = null, hiTail = null;
            int lc = 0, hc = 0;
            for (TreeNode<K,V> e = b, next; e != null; e = next) {
                next = (TreeNode<K,V>)e.next;
                e.next = null;
                if ((e.hash & bit) == 0) {
                    if ((e.prev = loTail) == null)
                        loHead = e;
                    else
                        loTail.next = e;
                    loTail = e;
                    ++lc;
                }
                else {
                    if ((e.prev = hiTail) == null)
                        hiHead = e;
                    else
                        hiTail.next = e;
                    hiTail = e;
                    ++hc;
                }
            }

            if (loHead != null) {
                if (lc <= UNTREEIFY_THRESHOLD)
                    tab[index] = loHead.untreeify(map);
                else {
                    tab[index] = loHead;
                    if (hiHead != null) // (else is already treeified)
                        loHead.treeify(tab);
                }
            }
            if (hiHead != null) {
                if (hc <= UNTREEIFY_THRESHOLD)
                    tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead;
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }

        /* --------------------------- 红黑树相关方法 --------------------------------- */
        /**
         * 下面所分析的红黑树模型, 是将红黑树转换为对应的4阶二叉树
         */

        /**
         * 【左旋转】
         *  使用于左旋转的场景:
         *    新增节点为
         */
        static <K,V> TreeNode<K,V> rotateLeft(TreeNode<K,V> root,
                                              TreeNode<K,V> p) {
            TreeNode<K,V> r, pp, rl;  //
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        /**
         * 右旋转
         */
        static <K,V> TreeNode<K,V> rotateRight(TreeNode<K,V> root,
                                               TreeNode<K,V> p) {
            TreeNode<K,V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        /**
         *  在红黑树插入节点后, 修复红黑树的性质
         *  root: 红黑树的新节点, x为新插入的节点
         *
         *【红黑树添加节点的12种情况】
         * 一些节点的定义:
         *      x:新增节点
         *      xp:新增节点的父节点
         *      xu: 新增节点的叔叔节点
         *      xpp:新增节点的祖父节点
         *      xppl:新增节点的祖父节点的左子节点 (新增节点的父节点或者叔叔节点)
         *      xppr:新增节点的祖父节点的右子节点 (新增节点的父节点或者叔叔节点)
         *
         * 【1】  xp节点为黑色, xp节点度为 0, x节点为左子节点  ==> 无需调整
         * 【2】  xp节点为黑色, xp节点度为 0, x节点为右子节点  ==> 无需调整
         * 【3】  xp节点为黑色, xp节点度为 1, x节点为左子节点  ==> 无需调整
         * 【4】  xp节点为黑色, xp节点度为 1, x节点为右子节点  ==> 无需调整
         *                                                                                               注意:这里的xp节点为旋转之后的xp节点, x节点为旋转之后的x节点
         * 【5】  xp节点为红色, xp节点度为 0, xp节点为(左)子节点, xpp节点为黑色, xpp节点度为 (1), x节点为(左)子节点  ==> xp节点右旋转, xp染为黑色, xpp染为红色
         * 【6】  xp节点为红色, xp节点度为 0, xp节点为(左)子节点, xpp节点为黑色, xpp节点度为 (1), x节点为(右)子节点  ==> xp节点先左旋转, 再右旋转, x染为黑色, xpp染为红色
         * 【7】  xp节点为红色, xp节点度为 0, xp节点为(右)子节点, xpp节点为黑色, xpp节点度为 (1), x节点为(左)子节点  ==> xp节点先右旋转, 再左旋转, x染为黑色, xpp染为红色
         * 【8】  xp节点为红色, xp节点度为 0, xp节点为(右)子节点, xpp节点为黑色, xpp节点度为 (1), x节点为(右)子节点  ==> xp节点左旋转, xp染为黑色, xpp染为红色
         *
         * 【9】  xp节点为红色, xp节点度为 0, xp节点为(左)子节点, xpp节点为黑色, xpp节点度为 (2), x节点为(左)子节点  ==> xp染为黑色, xu染为黑色, xpp染为红色, 然后以 xpp为新增节点x继续修复红黑树性质
         * 【10】 xp节点为红色, xp节点度为 0, xp节点为(左)子节点, xpp节点为黑色, xpp节点度为 (2), x节点为(右)子节点  ==> xp染为黑色, xu染为黑色, xpp染为红色, 然后以 xpp为新增节点x继续修复红黑树性质
         * 【11】 xp节点为红色, xp节点度为 0, xp节点为(右)子节点, xpp节点为黑色, xpp节点度为 (2), x节点为(左)子节点  ==> xp染为黑色, xu染为黑色, xpp染为红色, 然后以 xpp为新增节点x继续修复红黑树性质
         * 【12】 xp节点为红色, xp节点度为 0, xp节点为(右)子节点, xpp节点为黑色, xpp节点度为 (2), x节点为(右)子节点  ==> xp染为黑色, xu染为黑色, xpp染为红色, 然后以 xpp为新增节点x继续修复红黑树性质
         *
         * ##为什么没有父节点为黑色, 父节点度为 2的情况 ?
         *  因为如果父节点为2, 那么还哪还有位置插入新的节点... 红黑树也是一个二叉树
         *
         * ##为什么没有父节点为红色, 父节点度不为 0 的情况 ?
         *  因为如果父节点为红色,且度不为 0, 那么这棵红黑树将不满足性质4 "RED节点的子节点都是BLACK"
         *  具体原因可以按照红黑树推导4阶B树分析:
         *       如果父节点为红色, 那么该节点将跟它的黑色节点合为一个B树节点, 如果 父节点为红色,且度不为 0, 那么红黑树将无法推导为一个标准的4阶B树
         */
        static <K,V> TreeNode<K,V> balanceInsertion(TreeNode<K,V> root, TreeNode<K,V> x) {
            /**
             * 默认插入的新节点为红色
             * 为什么是红色呢 ?
             *   因为默认为红色,可以满足红黑树五大性质中的四条,"RED节点的子节点都是BLACK" 这条除外
             */
            x.red = true;
            for (TreeNode<K,V> xp, xpp, xppl, xppr;;) {
                /**
                 * xp:新增节点的父节点
                 * xu:新增节点的叔叔节点
                 * xpp:新增节点的祖父节点
                 * xppl:新增节点的祖父节点的左子节点 (新增节点的父节点或者叔叔节点)
                 * xppr:新增节点的祖父节点的右子节点 (新增节点的父节点或者叔叔节点)
                 */
                if ((xp = x.parent) == null) {
                    x.red = false; //如果新增节点的父节点为空, 那么新增节点为根节点, 红黑树中根节点必须为黑色, 直接返回即可
                    return x;
                }
                /**
                 * 添加节点不为根节点情况
                 */
                else if (!xp.red || (xpp = xp.parent) == null)
                    /**
                     * xp节点为黑色, 或者父节点为root节点(黑色), 不需要调整
                     *  情况:【1】【2】【3】【4】
                     */
                    return root;

                if (xp == (xppl = xpp.left)) {
                    /**
                     * xp节点为左子节点
                     */
                    if ((xppr = xpp.right) != null && xppr.red) {
                        /**
                         * [xp节点为左子节点], xpp节点的度为 2, xu节点为红色
                         * 注意: 此时xu节点必为红色, 如果为黑色,则该红黑树将不满则性质"从任一节点到叶子节点的所有路径都包含相同数目的 BLACK节点"
                         * 情况:【9】【10】
                         */
                        xppr.red = false;  //xu节点染为黑色
                        xp.red = false;    //父节点染为黑色
                        xpp.red = true;    // 祖父节点染为红色
                        x = xpp;    // 将xpp节点当做新增节点,调整红黑树平衡 (4阶B树中的上溢)
                    }
                    else {
                        /**
                         * [xp节点为左子节点], xpp节点的度为 1
                         * 情况【6】
                         */
                        if (x == xp.right) {
                            /**
                             * [xp节点为左子节点, xpp节点的度为 1], x节点为右子节点(1)  ==>左旋转
                             */
                            root = rotateLeft(root, x = xp);  //先进行左旋转
                            //左旋之后,需要更新xp和xpp的引用节点为: 现xp节点为原x节点, 现x节点为原xp节点, xpp节点为现xp节点(原x节点)的父节点
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }


                        if (xp != null) {
                            /**
                             * [xp节点为左子节点, xpp节点的度为 1], x节点为左子节点
                             * 情况:【5】
                             * [xp节点为左子节点, xpp节点的度为 1], x节点为右子节点(2)  ==>右旋转
                             * 情况:【6】
                             */
                            xp.red = false;               //xp节点(原x节点)染为黑色
                            if (xpp != null) {
                                xpp.red = true;           //xpp节点染为红色
                                root = rotateRight(root, xpp);  //再进行右旋转
                            }
                        }
                    } //else
                }

                /**
                 * xp节点为右子节点
                 */
                else {
                    if (xppl != null && xppl.red) {
                        /**
                         * [xp节点为右子节点], xpp节点度为 2, xu节点为红色
                         * 情况【11】【12】
                         */
                        xppl.red = false;  //xu节点染为黑色
                        xp.red = false;    //xp节点然为黑色
                        xpp.red = true;    //xpp染为红色
                        x = xpp;   // 将xpp节点当做新增节点,调整红黑树平衡 (4阶B树中的上溢)
                    }
                    else {
                        /**
                         * [xp节点为右子节点], xpp节点度为 1
                         */
                        if (x == xp.left) {
                            /**
                             * [xp节点为右子节点, xpp节点度为 1], x节点为左子节点(1)
                             */
                            root = rotateRight(root, x = xp);  //右旋转
                            //右旋之后,需要更新xp和xpp的引用节点为: 现xp节点为原x节点, 现x节点为原xp节点, xpp节点为现xp节点(原x节点)的父节点
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            /**
                             *  [xp节点为右子节点, xpp节点度为 1], x节点为右子节点
                             *  情况:【8】
                             *  [xp节点为右子节点, xpp节点度为 1], x节点为左子节点(2)
                             *  情况:【7】
                             */
                            xp.red = false;  // xp染为黑色
                            if (xpp != null) {
                                xpp.red = true; //xpp染为红色
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        /**
         * 在红黑树删除节点后, 修复红黑树
         *
         *【红黑树删除节点的8种情况】
         * 一些节点的定义:
         *      x:删除节点
         *      xp:删除节点的父节点
         *      xu: 删除节点的叔叔节点
         *      xpr:删除节点的父节点
         *      xpl:删除节点的父节点
         *
         * 【1】 x节点为红色, x节点为左子节点, xp节点的度为 1  ==>无需调整
         * 【2】 x节点为红色, x节点为左子节点, xp节点的度为 2  ==>无需调整
         * 【3】 x节点为红色, x节点为右子节点, xp节点的度为 1  ==>无需调整
         * 【4】 x节点为红色, x节点为右子节点, xp节点的度为 2  ==>无需调整
         *
         * 【5】 x节点为黑色, x节点为左子节点, x节点的度为 1
         * 【6】 x节点为黑色, x节点为左子节点, x节点的度为 2
         * 【7】 x节点为黑色, x节点为右子节点, x节点的度为 1
         * 【8】 x节点为黑色, x节点为右子节点, x节点的度为 0
         *
         * 为什么只有8种情况 ? 不是应该红黑树中的每一个节点都有可能会被删除的吗 ?
         *   因为, 在红黑树中, 如果删除一个度为2的节点, 实际上删除的是它的前驱节点, 或者后继节点
         *
         */
        static <K,V> TreeNode<K,V> balanceDeletion(TreeNode<K,V> root, TreeNode<K,V> x) {
            /**
             * xp: 待删除节点的父节点
             * xpl: 待删除节点的父节点的左子节点
             * xpr: 待删除节点的父节点的右子节点
             */
            for (TreeNode<K,V> xp, xpl, xpr;;)  {
                if (x == null || x == root)
                    /**
                     * 如果待删除节点为根节点, 则无需调整
                     */
                    return root;
                else if ((xp = x.parent) == null) {

                    x.red = false;
                    return x;
                }
                else if (x.red) {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                            (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }
                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                    null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                            (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        }
                        else {
                            if (sl == null || !sl.red) {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                    null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * 验证红黑树的准确性
         */
        static <K,V> boolean checkInvariants(TreeNode<K,V> t) {
            // tp:父节点, tl:左子节点, tr:右子节点, tb:前驱节点, tn:后继节点
            TreeNode<K,V> tp = t.parent, tl = t.left, tr = t.right,
                tb = t.prev, tn = (TreeNode<K,V>)t.next;
            /**
             * 当出现以下任一情况时, 红黑树或者双向链表不正确
             */

            /**
             * 1、如果前驱节点存在, 但是前驱节点的后继节点不是当前节点
             */
            if (tb != null && tb.next != t)
                return false;
            /**
             * 2、如果后继节点存在, 但是后继节点的前驱节点不是当前节点
             */
            if (tn != null && tn.prev != t)
                return false;
            /**
             * 3、父节点存在, 但是父节点的左子节点、右子节点均不是当前节点
             */
            if (tp != null && t != tp.left && t != tp.right)
                return false;
            /**
             * 4、左子节点存在, 但是左子节点的父节点不是当前节点或者左子节点的hash值大于当前节点的hash值
             */
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            /**
             * 5、右子节点存在, 但是右子节点的父节点不是当前节点或者右子节点的hash值小于当前节点的hash值
             */
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            /**
             * 6、当前节点是红色,孩子节点也是红色  ==>红黑树性质
             */
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            /**
             * 递归验证左子树
             */
            if (tl != null && !checkInvariants(tl))
                return false;
            /**
             * 递归验证右子树
             */
            if (tr != null && !checkInvariants(tr))
                return false;
            /**
             * 通过验证, 返回true
             */
            return true;
        }
    }

}
