import * as React from "react";

const widgetModules = new Map();
const dummySession = {};

export const EnvPosContext = React.createContext({ line: 0, character: 0 });

export function useRpcSession() {
  return dummySession;
}

export function mapRpcError(error) {
  if (error instanceof Error) {
    return error;
  }
  return { message: String(error) };
}

export function useAsyncPersistent(factory, deps) {
  const [state, setState] = React.useState({ state: "loading" });

  React.useEffect(() => {
    let active = true;
    setState({ state: "loading" });
    Promise.resolve()
      .then(factory)
      .then(
        (value) => {
          if (active) {
            setState({ state: "resolved", value });
          }
        },
        (error) => {
          if (active) {
            setState({ state: "rejected", error });
          }
        },
      );
    return () => {
      active = false;
    };
  }, deps);

  return state;
}

export function registerWidgetModule(hash, moduleObject) {
  widgetModules.set(String(hash), moduleObject);
}

export async function importWidgetModule(_session, _pos, hash) {
  const moduleObject = widgetModules.get(String(hash));
  if (!moduleObject) {
    throw new Error("No static widget module registered for hash " + String(hash));
  }
  return moduleObject;
}

function taggedTextToString(taggedText) {
  if (taggedText == null) {
    return "";
  }
  if (typeof taggedText === "string") {
    return taggedText;
  }
  if (Array.isArray(taggedText)) {
    return taggedText.map(taggedTextToString).join("");
  }
  if (typeof taggedText !== "object") {
    return String(taggedText);
  }
  if ("text" in taggedText) {
    return String(taggedText.text);
  }
  if ("append" in taggedText && Array.isArray(taggedText.append)) {
    return taggedText.append.map(taggedTextToString).join("");
  }
  if ("tag" in taggedText) {
    const value = taggedText.tag;
    if (Array.isArray(value)) {
      if (value.length >= 2) {
        return taggedTextToString(value[1]);
      }
      if (value.length === 1) {
        return taggedTextToString(value[0]);
      }
    }
    return taggedTextToString(value);
  }
  return "";
}

function taggedTextToReact(taggedText, key = "0") {
  if (taggedText == null) {
    return null;
  }
  if (typeof taggedText === "string") {
    return taggedText;
  }
  if (Array.isArray(taggedText)) {
    return taggedText.map((child, index) => taggedTextToReact(child, `${key}-${index}`));
  }
  if (typeof taggedText !== "object") {
    return String(taggedText);
  }
  if ("text" in taggedText) {
    return String(taggedText.text);
  }
  if ("append" in taggedText && Array.isArray(taggedText.append)) {
    return taggedText.append.map((child, index) => taggedTextToReact(child, `${key}-${index}`));
  }
  if ("tag" in taggedText) {
    const value = taggedText.tag;
    if (Array.isArray(value) && value.length >= 2) {
      const tagInfo = value[0];
      const child = value[1];
      const props = { key, className: "sd-tagged" };
      if (tagInfo && typeof tagInfo === "object") {
        if ("subexprPos" in tagInfo) {
          props["data-subexpr-pos"] = String(tagInfo.subexprPos);
        }
        if ("info" in tagInfo) {
          props["data-tag-info"] = JSON.stringify(tagInfo.info);
        }
      }
      return React.createElement("span", props, taggedTextToReact(child, `${key}-0`));
    }
    return React.createElement(
      "span",
      { key, className: "sd-tagged" },
      taggedTextToReact(value, `${key}-0`),
    );
  }
  return taggedTextToString(taggedText);
}

export function InteractiveCode(props) {
  return React.createElement(
    "code",
    { className: "sd-inline-code" },
    taggedTextToReact(props?.fmt),
  );
}
