package org.omg.IOP;


/**
* org/omg/IOP/ServiceIdHelper.java .
* Generated by the IDL-to-Java compiler (portable), version "3.2"
* from c:/re/workspace/8-2-build-windows-amd64-cygwin/jdk8u91/6644/corba/src/share/classes/org/omg/PortableInterceptor/IOP.idl
* Friday, April 1, 2016 12:59:26 AM PDT
*/


/** A service id, represented as an int */
abstract public class ServiceIdHelper
{
  private static String  _id = "IDL:omg.org/IOP/ServiceId:1.0";

  public static void insert (org.omg.CORBA.Any a, int that)
  {
    org.omg.CORBA.portable.OutputStream out = a.create_output_stream ();
    a.type (type ());
    write (out, that);
    a.read_value (out.create_input_stream (), type ());
  }

  public static int extract (org.omg.CORBA.Any a)
  {
    return read (a.create_input_stream ());
  }

  private static org.omg.CORBA.TypeCode __typeCode = null;
  synchronized public static org.omg.CORBA.TypeCode type ()
  {
    if (__typeCode == null)
    {
      __typeCode = org.omg.CORBA.ORB.init ().get_primitive_tc (org.omg.CORBA.TCKind.tk_ulong);
      __typeCode = org.omg.CORBA.ORB.init ().create_alias_tc (org.omg.IOP.ServiceIdHelper.id (), "ServiceId", __typeCode);
    }
    return __typeCode;
  }

  public static String id ()
  {
    return _id;
  }

  public static int read (org.omg.CORBA.portable.InputStream istream)
  {
    int value = (int)0;
    value = istream.read_ulong ();
    return value;
  }

  public static void write (org.omg.CORBA.portable.OutputStream ostream, int value)
  {
    ostream.write_ulong (value);
  }

}
